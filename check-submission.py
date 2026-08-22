#!/usr/bin/env python3
"""Check this repository against the Palomar registry's mechanical requirements.

Palomar (https://palomar-registry.org/) verifies a submission before any editorial review, and
the checks below are the ones that fail *closed* — a missing licence or a malformed `sources`
list is rejected before a human or a model ever reads the mathematics. They are transcribed
from `PalomarRegistry/PalomarPolicy` `CONTRIBUTING.md` sections 2 and 3 and from the
mathlib-initiative `formalization.yaml` v0.4 schema.

This is a lint, not the verifier: Palomar rebuilds the project, runs leanprover/comparator, and
replays every proof through Lean's kernel and NanoDa. Use `verify.sh` for that half locally.

    python3 check-submission.py            # offline: skips the taxonomy snapshots
    python3 check-submission.py --online   # also validates arXiv/MSC codes against Palomar's

The submission itself names three repository-relative paths, which are also checked here:

    selected project      comparator
    comparator config     comparator/config.json
    metadata              formalization.yaml
"""

from __future__ import annotations

import argparse
import io
import json
import os
import re
import subprocess
import sys

import yaml

PROJECT = "comparator"
CONFIG = "comparator/config.json"
METADATA = "formalization.yaml"
MIN_TOOLCHAIN = (4, 28, 0)
RELATIONSHIPS = {"formalizes", "adapts", "independently-proves", "background", "other"}
SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}
METHODS = {"manual", "copilot", "agent", "autonomous", "other"}
LICENCE_RE = re.compile(r"(?i)\A(licen[cs]e|copying|unlicense|ofl)(\.(md|markdown|txt))?\Z")

failures: list[str] = []
warnings: list[str] = []


def check(cond: object, msg: str) -> bool:
    print(("  pass  " if cond else "  FAIL  ") + msg)
    if not cond:
        failures.append(msg)
    return bool(cond)


def warn(cond: object, msg: str) -> None:
    if not cond:
        print("  warn  " + msg)
        warnings.append(msg)


class NoDuplicates(yaml.SafeLoader):
    """Palomar rejects duplicate mapping keys; PyYAML silently keeps the last."""


def _no_dup(loader, node, deep=False):
    seen = set()
    for key, _ in node.value:
        k = loader.construct_object(key, deep=True)
        if k in seen:
            raise ValueError(f"duplicate mapping key: {k!r}")
        seen.add(k)
    return yaml.SafeLoader.construct_mapping(loader, node, deep)


NoDuplicates.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _no_dup)


def taxonomies() -> tuple[dict, dict] | None:
    """Palomar's checked-in arXiv and MSC2020 snapshots, via the GitHub API."""
    def fetch(path: str) -> dict:
        raw = subprocess.run(
            ["gh", "api", f"repos/PalomarRegistry/PalomarSubmission/contents/{path}",
             "--jq", ".content"],
            capture_output=True, text=True, timeout=120, check=True).stdout
        import base64
        return json.loads(base64.b64decode(raw.replace("\n", "")))
    try:
        return fetch("taxonomies/arxiv-categories.json"), fetch("taxonomies/msc2020-codes.json")
    except Exception as exc:  # network, gh auth, rate limit
        warnings.append(f"could not fetch Palomar's taxonomy snapshots ({exc.__class__.__name__})")
        return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--online", action="store_true",
                    help="validate arXiv/MSC codes against Palomar's checked-in snapshots")
    args = ap.parse_args()
    os.chdir(os.path.dirname(os.path.abspath(__file__)))

    print(f"== {METADATA}: shape ==")
    blob = open(METADATA, "rb").read()
    check(len(blob) <= 256 * 1024, f"at most 256 KiB ({len(blob)} bytes)")
    try:
        blob.decode("utf-8")
        check(True, "valid UTF-8")
    except UnicodeDecodeError:
        check(False, "valid UTF-8")
    try:
        meta = yaml.load(io.BytesIO(blob), NoDuplicates)
        check(True, "parses, with no duplicate mapping keys")
    except Exception as exc:
        check(False, f"parses, with no duplicate mapping keys ({exc})")
        return 1
    check(isinstance(meta, dict), "one top-level mapping")
    check(meta.get("version") == "v0.4", "version: v0.4")

    print("\n== fields Palomar checks mechanically ==")
    proj = meta.get("project") or {}
    check(isinstance(proj.get("name"), str) and proj["name"].strip(), "project.name is a nonempty string")
    desc = proj.get("description")
    check(isinstance(desc, str) and 0 < len(desc) <= 10_000,
          f"project.description is 1..10000 characters ({len(desc) if isinstance(desc, str) else 'missing'})")
    for field in ("authors", "responsible_maintainers"):
        val = proj.get(field)
        check(isinstance(val, list) and val and all(isinstance(x, str) and x.strip() for x in val),
              f"project.{field} is a nonempty list of nonempty names")
    check(isinstance(proj.get("license"), str) and proj["license"].strip(),
          f"project.license is set ({proj.get('license')})")
    for legacy, current in (("responsible_maintainer", "project.responsible_maintainers"),):
        check(legacy not in proj, f"no legacy alias project.{legacy}; use {current}")

    cls = meta.get("classification") or {}
    arxiv, msc = cls.get("arxiv") or [], cls.get("msc2020") or []
    check(1 <= len(arxiv) <= 2 and len(set(arxiv)) == len(arxiv),
          f"classification.arxiv is one or two distinct codes {arxiv}")
    check(1 <= len(msc) <= 8 and len(set(msc)) == len(msc),
          f"classification.msc2020 is one to eight distinct codes {msc}")
    if args.online:
        snap = taxonomies()
        if snap:
            ax, ms = snap
            check(all(c in ax for c in arxiv), "every arXiv code is in Palomar's snapshot")
            check(all(c in ms for c in msc), "every MSC2020 code is in Palomar's snapshot")

    methods = (meta.get("automation") or {}).get("methods")
    check(isinstance(methods, list) and methods
          and all(isinstance(m, dict) and str(m.get("method", "")).strip() for m in methods),
          "automation.methods is a nonempty list, each entry with a nonempty method")
    if isinstance(methods, list):
        warn(all(m.get("method") in METHODS for m in methods if isinstance(m, dict)),
             "a method outside {manual, copilot, agent, autonomous, other} is accepted but is not a standard category")
    check(str((meta.get("review") or {}).get("status", "")).strip(), "review.status is a nonempty string")

    print("\n== provenance: exactly one origin ==")
    sources = meta.get("sources")
    if not check(isinstance(sources, list) and sources, "sources is a nonempty list"):
        sources = []
    check(all(str(s.get("title", "")).strip() for s in sources), "every source has a nonempty title")
    check(all(s.get("relationship") in RELATIONSHIPS for s in sources),
          "every source relationship is in the closed vocabulary")
    check(all("type" not in s or s["type"] in SOURCE_TYPES for s in sources),
          "every declared source type is in the closed vocabulary")
    check(all("author" not in s for s in sources), "no legacy sources[].author alias; use authors")
    for s in sources:
        for c in s.get("contributors", []) or []:
            check(str(c.get("name", "")).strip() and 0 < len(str(c.get("role", ""))) <= 200,
                  "every source contributor has a name and a role of at most 200 characters")
    original = [s for s in sources if s.get("type") == "original-proof"]
    alt_original = bool(original) and all(s.get("relationship") == "other" for s in original) \
        and all(s.get("relationship") in {"background", "other"} for s in sources)
    alt_sourced = not original and any(
        s.get("relationship") in {"formalizes", "adapts", "independently-proves"} for s in sources)
    origin = "original" if alt_original else "source-based" if alt_sourced else "NEITHER"
    check(alt_original ^ alt_sourced, f"exactly one origin alternative holds -> result_origin: {origin}")
    check("provenance" not in meta, "no obsolete top-level provenance block")
    repo = meta.get("repository")
    if repo is None:
        check(True, "repository omitted -> this repository is the substantive development")
    else:
        sub = repo.get("substantive_formalization") or {}
        if repo.get("role") == "thin-wrapper" or sub:
            check(bool(str(sub.get("id", "")).strip()), "repository.substantive_formalization.id is set")
            check(re.fullmatch(r"[0-9a-f]{40}", str(sub.get("revision", ""))) is not None,
                  "repository.substantive_formalization.revision is a full lowercase 40-character SHA")

    print("\n== repository layout ==")
    licences = [f for f in os.listdir(".") if LICENCE_RE.match(f)]
    check(len(licences) == 1, f"exactly one conventional licence file at the repository root: {licences}")
    if len(licences) == 1:
        path = licences[0]
        check(os.path.isfile(path) and not os.path.islink(path)
              and 0 < os.path.getsize(path) <= 1024 * 1024,
              "the licence is a regular, non-symlink, nonempty file of at most 1 MiB")
        head = open(path, encoding="utf-8", errors="replace").read(4000)
        spdx = "Apache-2.0" if "Apache License" in head and "Version 2.0" in head else None
        check(spdx is not None and spdx == proj.get("license"),
              f"the licence file and project.license agree ({spdx} / {proj.get('license')})")

    check(os.path.isdir(PROJECT), f"the selected project {PROJECT}/ is a directory")
    lakefiles = [f for f in os.listdir(PROJECT) if f in ("lakefile.toml", "lakefile.lean")]
    check(len(lakefiles) == 1, f"the selected project has exactly one lakefile: {lakefiles}")
    check(os.path.isfile(f"{PROJECT}/lake-manifest.json"),
          "the selected project commits its own lake-manifest.json")
    toolchain = open(f"{PROJECT}/lean-toolchain").read().strip()
    # `lean4` in the package name would eat the major version, so anchor on the release tag
    release = re.search(r"v(\d+)\.(\d+)\.(\d+)", toolchain)
    version = tuple(int(g) for g in release.groups()) if release else ()
    check(version >= MIN_TOOLCHAIN,
          f"the toolchain {toolchain} is at least v{'.'.join(map(str, MIN_TOOLCHAIN))}")

    # A packagesDir above the selected project is the failure that is invisible locally: it works
    # against a repository that already has a built package tree at the root, and turns the first
    # dependency fetch into a write outside the project everywhere else.
    for spec in (f"{PROJECT}/lakefile.toml", f"{PROJECT}/lake-manifest.json"):
        if not os.path.isfile(spec):
            continue
        text = open(spec, encoding="utf-8").read()
        found = re.search(r"packagesDir\"?\s*[:=]\s*\"([^\"]+)\"", text)
        inside = found is None or not os.path.relpath(
            os.path.join(PROJECT, found.group(1)), PROJECT).startswith("..")
        check(inside, f"{spec}: packagesDir stays inside the selected project"
                      + (f" (found {found.group(1)!r})" if found and not inside else ""))

    cfg = json.load(open(CONFIG))
    check(CONFIG.startswith(PROJECT + "/") and CONFIG.endswith(".json"),
          f"the comparator config {CONFIG} is inside the selected project and ends in .json")
    challenge, solution = cfg.get("challenge_module"), cfg.get("solution_module")
    check(challenge and solution and challenge != solution,
          f"Challenge and Solution are distinct modules ({challenge} / {solution})")
    check(set(cfg.get("permitted_axioms", [])) <= {"propext", "Quot.sound", "Classical.choice"},
          "permitted_axioms are within the standard three")
    src = f"{PROJECT}/{challenge}.lean"
    if check(os.path.isfile(src), f"the Challenge source {src} exists"):
        lines, size = sum(1 for _ in open(src)), os.path.getsize(src)
        check(lines <= 1000 and size <= 100 * 1024,
              f"the Challenge is within the hard limits ({lines} lines, {size} bytes)")
        warn(lines <= 300 and size <= 32 * 1024,
             f"the Challenge is over the soft limit ({lines} lines, {size} bytes; "
             "a mechanical warning, not a failure — it is harder to audit)")

    print()
    for w in warnings:
        print("WARNING: " + w)
    if failures:
        print(f"\n{len(failures)} mechanical requirement(s) not met:")
        for f in failures:
            print("  - " + f)
        return 1
    print("Mechanically ready to submit"
          + (f", with {len(warnings)} warning(s)" if warnings else "")
          + f". Origin: {origin}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
