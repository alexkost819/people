#!/usr/bin/env python3
"""Fill missing legislator office phones from the legislature's own data.

For each current legislator in data/<state>/legislature whose offices have
no `voice`, look the member up in the legislature's official API, roster or
member page, confirm it is the same person by matching email, and add the
published phone to their office. The page the number came from is added to
`sources` when it isn't there.

Only the office lines (and one `sources` line) are touched; the rest of
the file is left byte-for-byte as it was, so diffs stay reviewable.

Dry run by default: prints what it would fill or skip, and why. Pass
--write to edit.

    uv run .github/scripts/fill_phones.py ks ms
    uv run .github/scripts/fill_phones.py ks --write
    uv run .github/scripts/fill_phones.py --self-test

Each state's route and rule is in its fetch_<state> function's docstring.
Members whose official record has no number, has several with no rule to
pick one, or whose email doesn't match are reported and left alone.

Session-specific values (_SESSION) need updating when a new legislature
is seated.

Why this exists, and TODO
-------------------------
The scheduled "People legislators update <st> <timestamp>" PRs (branch
automatic-legislators-updates-<st>-..., opened by openstates-bot) are not
scraper output. Since 2025-02 their commits are authored by
root@legistorm-to-openstates-legislators-*: a job outside the public repos
that imports LegiStorm's data. Maintainers bundle them into an
auto-merge-* branch, fix lint and merge (.claude/agents/people-merge.md,
resolve-lint.md); on push to main, update-database.yml runs
`os-people to-csv --upload`. That job has removed hand-added phones
(openstates/issues#1453) and set `image:` to news-site photos (#4207, SD).

The people scrapers still exist but nothing in these PRs comes from them:

1. openstates-scrapers/scrapers_next/<st>/people.py writes one JSON file
   per person.
2. `os-people merge <abbr> <dir>` (openstates-core, cli/people.py) matches
   it to the YAML here, updates changed fields, merges offices field by
   field (utils/people/merge.py update_office, so a scraped phone fills an
   empty office), adds new people and retires unmatched ones.

Some scrapers have also drifted from their sites:

- KS: reads OFFPH but still calls the v11 API and links to the b2023_24
  session.
- AL: its GraphQL query no longer works; fetch_al uses the query the
  current site uses.

The official sources used here carry more than phones (party, district,
email, active status, photos, committees, leadership), which the
scrapers could pick up too.

TODO: retire this script by either
  (a) reviving the people scrapers (KS and AL first) and running
      scrape + merge on a schedule again, or
  (b) moving the people scrapers into this repo so they run, and are
      fixed, next to the data they write.
Until then, keep each fetch_<state> on the same route its scraper uses
(or should use), so the logic can move into the scraper as is.
"""

from __future__ import annotations

import argparse
import datetime
import json
import re
import socket
import ssl
import sys
import unicodedata
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections.abc import Callable
from dataclasses import dataclass
from functools import cache
from itertools import pairwise
from pathlib import Path

import lxml.html
import yaml
from cryptography import x509
from cryptography.x509.oid import AuthorityInformationAccessOID

_USER_AGENT = "openstates-people-fill-phones/1.0 (https://github.com/openstates/people)"
_PHONE_DIGITS = 10
_DATA = Path(__file__).resolve().parents[2] / "data"

# Update when a new legislature is seated.
_SESSION = {
    "ma": "194",  # General Court
    "sd": "71",  # SessionMembers session id
    "wi": "2025",
    "wy": "2025",
}

# Top-level keys that follow `offices` in person files, in dump order.
_KEYS_AFTER_OFFICES = (
    "links",
    "other_names",
    "ids",
    "other_identifiers",
    "sources",
    "extras",
)


@dataclass
class Found:
    voice: str  # NNN-NNN-NNNN
    field: str  # which source field the number came from
    source_url: str  # official page to cite in `sources`
    address: str | None = None  # used only when a new office is made
    # Offices the number may go on, in order of preference. With none of
    # them present, a new office of the first classification is added.
    targets: tuple[str, ...] = ("capitol",)


class EditCheckError(Exception):
    def __init__(self, problem: str) -> None:
        super().__init__(f"post-edit check failed: {problem}")


# --- fetching ---------------------------------------------------------------


def _get(url: str, data: bytes | None = None, headers: dict | None = None) -> bytes:
    req = urllib.request.Request(  # noqa: S310
        url, data=data, headers={"User-Agent": _USER_AGENT, **(headers or {})}
    )
    host = urllib.parse.urlsplit(url).hostname or ""
    with urllib.request.urlopen(req, timeout=30, context=_tls(host)) as resp:  # noqa: S310
        return resp.read()


@cache
def _get_cached(url: str) -> bytes:
    return _get(url)


@cache
def _tls(host: str) -> ssl.SSLContext:
    """Verifying TLS context, completing the chain for servers that omit it.

    Some legislature servers (billstatus.ls.state.ms.us) don't send their
    intermediate certificate. Fetch it from the leaf certificate's AIA
    "CA Issuers" URL, as browsers do. Verification stays on: the
    intermediate still has to chain to a trusted root.
    """
    ctx = ssl.create_default_context()
    try:
        with socket.create_connection((host, 443), timeout=30) as sock:
            ctx.wrap_socket(sock, server_hostname=host).close()
    except ssl.SSLCertVerificationError:
        leaf = x509.load_pem_x509_certificate(
            ssl.get_server_certificate((host, 443)).encode()
        )
        aia = leaf.extensions.get_extension_for_class(
            x509.AuthorityInformationAccess
        ).value
        for desc in aia:
            if desc.access_method == AuthorityInformationAccessOID.CA_ISSUERS:
                url = desc.access_location.value
                with urllib.request.urlopen(url, timeout=30) as issuer:  # noqa: S310
                    ctx.load_verify_locations(cadata=issuer.read())  # DER bytes
    return ctx


def _html(url: str) -> lxml.html.HtmlElement:
    return lxml.html.fromstring(_get_cached(url))


def _tokens(el: lxml.html.HtmlElement) -> list[str]:
    """Visible text pieces of an element, in document order."""
    return [t.strip() for t in el.itertext() if t.strip()]


def _phone(raw: str | None) -> str | None:
    digits = re.sub(r"\D", "", raw or "")
    if len(digits) == _PHONE_DIGITS + 1 and digits.startswith("1"):
        digits = digits[1:]
    if len(digits) != _PHONE_DIGITS:
        return None
    return f"{digits[:3]}-{digits[3:6]}-{digits[6:]}"


def _urls(person: dict) -> list[str]:
    return [x["url"] for key in ("links", "sources") for x in person.get(key) or []]


def _find_url(person: dict, pattern: str) -> re.Match | None:
    return next(
        (m for u in _urls(person) if (m := re.search(pattern, u, re.IGNORECASE))),
        None,
    )


def _norm(email: str | None) -> str:
    """Compare emails case-insensitively and ignoring hyphens: WI lists
    rep.rivera-wagner@ where the file has rep.riverawagner@."""
    return (email or "").strip().lower().replace("-", "")


def _email(person: dict) -> str:
    return _norm(person.get("email"))


def _by_email(rows: dict[str, dict], person: dict) -> dict | str:
    if not _email(person):
        return "no email in file to match on"
    found = {_norm(k): v for k, v in rows.items()}.get(_email(person))
    return found or f"no member with email {person.get('email')}"


# --- states -----------------------------------------------------------------


@cache
def _al_members() -> dict[str, dict]:
    query = (
        "{legislativeMembers(where:{active:{eq:true}})"
        "{data{id body district phone email fullAddress}}}"
    )
    body = _get(
        "https://gql.api.alison.legislature.state.al.us/graphql",
        data=json.dumps({"query": query}).encode(),
        headers={
            "Content-Type": "application/json",
            "Referer": "https://alison.legislature.state.al.us/",
        },
    )
    rows = json.loads(body)["data"]["legislativeMembers"]["data"]
    return {r["email"].strip().lower(): r for r in rows if r.get("email")}


def fetch_al(person: dict) -> Found | str:
    """AL Legislature GraphQL API, `legislativeMembers`: `phone`."""
    row = _by_email(_al_members(), person)
    if isinstance(row, str):
        return row
    if not (voice := _phone(row["phone"])):
        return "no phone published"
    address = ", ".join(x.strip() for x in (row["fullAddress"] or "").splitlines())
    return Found(
        voice,
        "phone",
        "https://gql.api.alison.legislature.state.al.us/graphql",
        address or None,
    )


@cache
def _co_members() -> list[dict]:
    url = "https://leg.colorado.gov/legislators"
    rows = []
    for tr in _html(url).xpath("//tr[td]"):
        cells = [c.text_content().strip() for c in tr.xpath("./td|./th")]
        href = [h for h in tr.xpath(".//a/@href") if h.startswith("/legislators/")]
        if len(cells) >= 6 and href:  # noqa: PLR2004 - roster has 6 columns
            chamber, name, district, _, phone, email = cells[:6]
            rows.append(
                {
                    "chamber": "upper" if chamber == "Senator" else "lower",
                    "surname": name.split(",")[0].strip().lower(),
                    "district": district,
                    "voice": _phone(phone),
                    "email": email.lower(),
                    "page": urllib.parse.urljoin(url, href[0]),
                }
            )
    return rows


def _current_role(person: dict) -> dict:
    return person["roles"][-1]


def fetch_co(person: dict) -> Found | str:
    """leg.colorado.gov/legislators roster: the Phone column, matched by
    email, or for a file with no email by chamber, district and surname.
    The new-office address is the Capitol address on the member's page."""
    rows = _co_members()
    if _email(person):
        match = [r for r in rows if _norm(r["email"]) == _email(person)]
    else:
        role = _current_role(person)
        surname = person.get("family_name", "").lower()
        match = [
            r
            for r in rows
            if (r["chamber"], r["district"]) == (role["type"], str(role["district"]))
            and _fold(r["surname"]) == _fold(surname)
        ]
    if len(match) != 1:
        return f"{len(match)} roster rows match"
    row = match[0]
    if not row["voice"]:
        return "no phone published"
    text = " ".join(_tokens(_html(row["page"])))
    m = re.search(r"Capitol address:\s*(.+?\d{5})", text)
    address = re.sub(r"\s+(Denver)", r", \1", m.group(1)) if m else None
    return Found(row["voice"], "roster Phone", row["page"], address)


def _fold(s: str) -> str:
    """Lowercase ASCII, so "González" matches the roster's "Gonzalez"."""
    return unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode().lower()


def fetch_ks(person: dict) -> Found | str:
    """KS Legislature member API: OFFPH (the Phone on the member page) and
    OFFICENUM (room). The new-office address is that room plus the street
    address in the site footer, 300 SW 10th Ave, Topeka, KS 66612."""
    pattern = r"kslegislature\.gov/li/b\d{4}_\d{2}/members/([a-z_]+_\d+)"
    if not (m := _find_url(person, pattern)):
        return "no kslegislature.gov member page in links/sources"
    api = f"https://www.kslegislature.gov/li/api/v13/rev-1/members/{m.group(1)}/"
    content = json.loads(_get(api))["content"]
    if _norm(content["EMAIL"]) != _email(person):
        return f"email mismatch: site {content['EMAIL']}"
    if not (voice := _phone(content["OFFPH"])):
        return "no OFFPH published"
    address = (
        f"Room {content['OFFICENUM']}, Kansas State Capitol, 300 SW 10th Ave, "
        "Topeka, KS 66612"
    )
    return Found(voice, "OFFPH", m.string.rstrip("/"), address)


def fetch_ma(person: dict) -> Found | str:
    """MA Legislature API, LegislativeMembers/<code>: PhoneNumber. The
    new-office address uses RoomNumber at the State House."""
    if not (m := _find_url(person, r"malegislature\.gov/Legislators/Profile/(\w+)")):
        return "no malegislature.gov profile in links/sources"
    api = (
        "https://malegislature.gov/api/GeneralCourts/"
        f"{_SESSION['ma']}/LegislativeMembers/{m.group(1)}"
    )
    data = json.loads(_get(api))
    if _norm(data.get("EmailAddress")) != _email(person):
        return f"email mismatch: site {data.get('EmailAddress')}"
    if not (voice := _phone(data.get("PhoneNumber"))):
        return f"no usable PhoneNumber: {data.get('PhoneNumber')!r}"
    room = data.get("RoomNumber")
    address = f"24 Beacon St., Room {room}; Boston, MA 02133" if room else None
    return Found(voice, "PhoneNumber", m.string, address)


def fetch_me(person: dict) -> Found | str:
    """ME House member profile, Contact Details: the member's only published
    number (labelled Home, Work, Cell, ...). Senators have no such page."""
    pattern = r"legislature\.maine\.gov/house/(house/)?MemberProfiles/Details/\d+"
    if not (m := _find_url(person, pattern)):
        return "no ME House member profile in links/sources"
    root = _html(m.string)
    emails = {
        _norm(h.removeprefix("mailto:"))
        for h in root.xpath("//a[starts-with(@href, 'mailto:')]/@href")
    }
    if _email(person) not in emails:
        return f"email mismatch: site {sorted(emails)}"
    tokens = _tokens(root)
    start = tokens.index("Contact Details") if "Contact Details" in tokens else 0
    end = tokens.index("Overview", start) if "Overview" in tokens[start:] else None
    block = tokens[start:end]
    phones = {
        label: v
        for label, value in pairwise(block)
        if label.endswith("Phone") and (v := _phone(value))
    }
    if len(set(phones.values())) == 1:
        label, voice = next(iter(phones.items()))
        return Found(voice, label, m.string)
    return "no number published" if not phones else f"several numbers: {phones}"


@cache
def _mn_house() -> dict[str, dict]:
    """house.mn.gov member list: name line, address lines, phone, email."""
    tokens = _tokens(_html("https://www.house.leg.state.mn.us/members/hmem.asp"))
    rows = {}
    for i, tok in enumerate(tokens):
        if tok == "E-mail:" and i + 1 < len(tokens):
            j = i - 1
            while j > 0 and not re.search(r"\(\w+, [^)]+\)$", tokens[j]):
                j -= 1
            voice = _phone(tokens[i - 1])
            if voice and tokens[i + 1].lower() not in rows:
                # the page repeats the list later without phones
                rows[tokens[i + 1].lower()] = {
                    "voice": voice,
                    "address": ", ".join(tokens[j + 1 : i - 1]),
                }
    return rows


@cache
def _mn_senate() -> dict[str, dict]:
    rows = json.loads(_get("https://www.senate.mn/api/members"))
    rows = rows.get("members", rows) if isinstance(rows, dict) else rows
    return {r["email"].lower(): r for r in rows if r.get("email")}


def fetch_mn(person: dict) -> Found | str:
    """House: house.mn.gov member list (the Capitol office phone). Senate:
    senate.mn members API, full_phone_number."""
    house = "@house.mn.gov" in _email(person)
    if house:
        row = _by_email(_mn_house(), person)
        if isinstance(row, str):
            return row
        voice, address = row["voice"], row["address"]
        m = _find_url(person, r"house\.mn\.gov/members/profile/\d+")
        source = m.string if m else "https://www.house.leg.state.mn.us/members/hmem.asp"
    else:
        row = _by_email(_mn_senate(), person)
        if isinstance(row, str):
            return row
        voice = _phone(row.get("full_phone_number"))
        address = "; ".join(
            x
            for x in (
                row.get("office_address_first_line"),
                row.get("office_address_second_line"),
            )
            if x
        )
        source = "https://www.senate.mn/api/members"
    if not voice:
        return "no phone published"
    return Found(voice, "office phone", source, address or None)


def fetch_ms(person: dict) -> Found | str:
    """MS member XML: CAP_PHONE; with none, the member's only published
    number (H_PHONE, B_PHONE or OTH_PHONE), which the member page shows as
    their contact."""
    pattern = r"billstatus\.ls\.state\.ms\.us/members/(house|senate)/[^/]+\.xml"
    if not (m := _find_url(person, pattern)):
        return "no billstatus member XML in links/sources"
    url = m.string
    root = ET.fromstring(_get(url))  # noqa: S314 - legislature's own XML
    chamber = m.group(1).lower()
    site_email = f"{(root.findtext('.//EMAIL_ADDRESS') or '').strip()}@{chamber}.ms.gov"
    if _norm(site_email) != _email(person):
        return f"email mismatch: site {site_email}"
    if voice := _phone(root.findtext("CAP_PHONE")):
        return Found(voice, "CAP_PHONE", url)
    others = {
        f: v
        for f in ("H_PHONE", "B_PHONE", "OTH_PHONE")
        if (v := _phone(root.findtext(f)))
    }
    if len(set(others.values())) == 1:
        field, voice = next(iter(others.items()))
        if field == "OTH_PHONE":
            field += f" ({root.findtext('OTH_TYPE') or '?'})"
        return Found(voice, field, url)
    return "no number published" if not others else f"several numbers: {others}"


_ND_COUNCIL_LINE = "701-328-2916"  # Legislative Council, ndlegis.gov footer


def fetch_nd(person: dict) -> Found | str:
    """ndlegis.gov biography page: Home, else Work, else Cell. A member who
    publishes none gets the Legislative Council line from the site footer.
    The number goes on the existing Capitol office (the bios give no
    mailing address)."""
    if not (m := _find_url(person, r"ndlegis\.gov/biography/[a-z0-9-]+")):
        return "no ndlegis.gov biography page in links/sources"
    tokens = _tokens(_html(m.string))
    pairs = dict(pairwise(tokens))
    if _norm(pairs.get("Email")) != _email(person):
        return f"email mismatch: site {pairs.get('Email')}"
    targets = ("capitol", "capitol-mail")
    for label in ("Home", "Work", "Cell"):
        if voice := _phone(pairs.get(label)):
            return Found(voice, label, m.string, targets=targets)
    return Found(
        _ND_COUNCIL_LINE, "Legislative Council line", m.string, targets=targets
    )


@cache
def _sd_members() -> dict[str, dict]:
    url = f"https://sdlegislature.gov/api/SessionMembers/Session/{_SESSION['sd']}"
    rows = json.loads(_get(url))
    return {r["EmailState"].lower(): r for r in rows if r.get("EmailState")}


def fetch_sd(person: dict) -> Found | str:
    """SD Legislature SessionMembers API: CapitolPhone. New offices get the
    Capitol address the other SD files use."""
    row = _by_email(_sd_members(), person)
    if isinstance(row, str):
        return row
    if not (voice := _phone(row.get("CapitolPhone"))):
        return "no CapitolPhone published"
    page = (
        f"https://sdlegislature.gov/Legislators/Profile/{row['SessionMemberId']}/Detail"
    )
    address = "Capitol Building 500 E. Capitol Ave., Pierre, SD 57501"
    return Found(voice, "CapitolPhone", page, address)


@cache
def _wi_members() -> dict[str, dict]:
    """WI roster pages: per member, Madison Office address and Telephone."""
    rows = {}
    for chamber in ("assembly", "senate"):
        url = (
            f"https://docs.legis.wisconsin.gov/{_SESSION['wi']}/legislators/{chamber}/"
        )
        tokens = _tokens(_html(url))
        for i, tok in enumerate(tokens):
            if tok != "Email" or i + 2 >= len(tokens):
                continue
            email = tokens[i + 2].lower()
            j = i
            while j > 0 and tokens[j] != "Madison Office":
                j -= 1
            block = tokens[j:i]
            if "Telephone" not in block:
                continue
            t = block.index("Telephone")
            rows[email] = {
                "voice": _phone(block[t + 2]),  # first number; the second is toll-free
                "address": ", ".join(x for x in block[2:t] if x != ":"),
                "source": url,
            }
    return rows


def fetch_wi(person: dict) -> Found | str:
    """WI Assembly and Senate roster pages: the Madison Office address and
    its first Telephone number (the second is toll-free)."""
    row = _by_email(_wi_members(), person)
    if isinstance(row, str):
        return row
    if not row["voice"]:
        return "no Madison Office phone published"
    return Found(
        row["voice"], "Madison Office Telephone", row["source"], row["address"]
    )


@cache
def _wy_members() -> dict[str, dict]:
    rows = {}
    for chamber in ("H", "S"):
        url = f"https://wyoleg.gov/LsoService/api/legislator/{_SESSION['wy']}/{chamber}"
        for r in json.loads(_get(url)):
            if r.get("eMail"):
                rows[r["eMail"].lower()] = {**r, "source": url}
    return rows


def fetch_wy(person: dict) -> Found | str:
    """WY LSO API, legislator/<year>/H and /S: `phone`, the one number each
    member publishes. It goes on the district office, which holds the
    member's mailing address."""
    row = _by_email(_wy_members(), person)
    if isinstance(row, str):
        return row
    if not (voice := _phone(row.get("phone"))):
        return "no phone published"
    address = None
    if row.get("address") and row.get("city"):
        address = f"{row['address']}; {row['city']}, WY {row.get('zip') or ''}".strip()
    return Found(
        voice,
        "phone",
        row["source"],
        address,
        targets=("district", "district-mail"),
    )


FETCHERS: dict[str, Callable[[dict], Found | str]] = {
    "al": fetch_al,
    "co": fetch_co,
    "ks": fetch_ks,
    "ma": fetch_ma,
    "me": fetch_me,
    "mn": fetch_mn,
    "ms": fetch_ms,
    "nd": fetch_nd,
    "sd": fetch_sd,
    "wi": fetch_wi,
    "wy": fetch_wy,
}


# --- editing ----------------------------------------------------------------


def _top_level(lines: list[str]) -> dict[str, int]:
    return {
        m.group(1): i
        for i, line in enumerate(lines)
        if (m := re.match(r"([a-z_]+):", line))
    }


def _dump(obj: object) -> list[str]:
    text = yaml.dump(obj, default_flow_style=False, sort_keys=False, allow_unicode=True)
    return text.splitlines(keepends=True)


def _new_office(found: Found) -> dict:
    office = {"classification": found.targets[0]}
    if found.address:
        office["address"] = found.address
    office["voice"] = found.voice
    return office


def add_phone(text: str, found: Found) -> str:
    """Return text with found.voice on the preferred office (made if absent)."""
    lines = text.splitlines(keepends=True)
    keys = _top_level(lines)
    person = yaml.safe_load(text)
    offices = person.get("offices") or []

    if "offices" not in keys:
        at = min(
            (keys[k] for k in _KEYS_AFTER_OFFICES if k in keys), default=len(lines)
        )
        lines[at:at] = _dump({"offices": [_new_office(found)]})
    elif not offices:  # `offices: []`
        start = keys["offices"]
        lines[start : start + 1] = _dump({"offices": [_new_office(found)]})
    else:
        start = keys["offices"]
        end = min((i for i in keys.values() if i > start), default=len(lines))
        entries = [i for i in range(start + 1, end) if lines[i].startswith("- ")]
        target = next(
            (
                entries[n]
                for cls in found.targets
                for n, o in enumerate(offices)
                if o.get("classification") == cls
            ),
            None,
        )
        if target is None:
            lines[end:end] = _dump([_new_office(found)])
        else:
            nxt = next((i for i in entries if i > target), end)
            # voice goes after classification/address, before fax/name
            at = next(
                (
                    i
                    for i in range(target + 1, nxt)
                    if re.match(r"  (fax|name):", lines[i])
                ),
                nxt,
            )
            lines[at:at] = [f"  voice: {found.voice}\n"]

    text = "".join(lines)
    if found.source_url not in {s["url"] for s in person.get("sources") or []}:
        lines = text.splitlines(keepends=True)
        start = _top_level(lines)["sources"]
        end = min(
            (i for i in _top_level(lines).values() if i > start), default=len(lines)
        )
        lines[end:end] = _dump([{"url": found.source_url}])
        text = "".join(lines)

    check = yaml.safe_load(text)
    if not any(
        o.get("classification") in found.targets and o.get("voice") == found.voice
        for o in check["offices"]
    ):
        raise EditCheckError("voice_not_set")
    before = [{k: v for k, v in o.items() if k != "voice"} for o in offices]
    after = [{k: v for k, v in o.items() if k != "voice"} for o in check["offices"]]
    if after[: len(before)] != before:
        raise EditCheckError("existing_offices_changed")
    untouched = ("offices", "sources")
    if {k: v for k, v in check.items() if k not in untouched} != {
        k: v for k, v in person.items() if k not in untouched
    }:
        raise EditCheckError("other_fields_changed")
    return text


def _missing_voice(person: dict) -> bool:
    today = datetime.date.today().isoformat()
    if not any(str(r.get("end_date") or "9999") >= today for r in person["roles"]):
        return False
    return not any((o.get("voice") or "").strip() for o in person.get("offices") or [])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("states", nargs="+", choices=sorted(FETCHERS))
    parser.add_argument("--write", action="store_true", help="edit the files")
    args = parser.parse_args()

    for state in args.states:
        for path in sorted((_DATA / state / "legislature").glob("*.yml")):
            text = path.read_text()
            person = yaml.safe_load(text)
            if not _missing_voice(person):
                continue
            try:
                found = FETCHERS[state](person)
            except Exception as e:  # noqa: BLE001 - report and keep going
                found = f"fetch failed: {e!r}"
            if isinstance(found, str):
                print(f"skip\t{state}\t{person['name']}\t{found}")
                continue
            print(
                f"fill\t{state}\t{person['name']}\t{found.voice}\t{found.field}"
                f"\t{found.source_url}"
            )
            if args.write:
                path.write_text(add_phone(text, found))
    return 0


def _selftest() -> None:
    """Check add_phone's office shapes and the sources append."""
    head = "id: ocd-person/x\nname: A\nroles:\n- type: lower\n  district: '1'\n"
    tail = "links:\n- url: https://a\nsources:\n- url: https://a\n"
    found = Found("555-555-0100", "T", "https://b#x", "Room #1, Capitol")
    new = (
        "offices:\n- classification: capitol\n"
        "  address: 'Room #1, Capitol'\n  voice: 555-555-0100\n"
    )
    cases = {
        "no offices": (head + tail, head + new + tail),
        "empty offices": (head + "offices: []\n" + tail, head + new + tail),
        "capitol without voice": (
            head
            + "offices:\n- classification: capitol\n  address: X\n"
            + "- classification: district\n  address: Y\n"
            + tail,
            head
            + "offices:\n- classification: capitol\n  address: X\n"
            + "  voice: 555-555-0100\n- classification: district\n  address: Y\n"
            + tail,
        ),
    }
    for name, (before, after) in cases.items():
        got = add_phone(before, found)
        assert got == after + "- url: https://b#x\n", name  # noqa: S101

    wy = Found("555-555-0100", "T", "https://a", targets=("district", "district-mail"))
    before = (
        head + "offices:\n- classification: capitol\n  address: X\n"
        "- classification: district-mail\n  address: Y\n" + tail
    )
    got = add_phone(before, wy)
    assert "  address: Y\n  voice: 555-555-0100\n" in got, "district target"  # noqa: S101
    assert "  address: X\n- classification" in got, "capitol untouched"  # noqa: S101
    print("selftest OK")


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        _selftest()
        raise SystemExit(0)
    raise SystemExit(main())
