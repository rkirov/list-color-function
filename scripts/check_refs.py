#!/usr/bin/env python3
"""Fail if a docstring names a Lean declaration that does not exist.

The kernel checks theorem statements. It does not look inside docstrings, so deleting a
declaration leaves every reference to it in prose dangling -- and the claim built around
that reference silently false. This catches the dangling name. It cannot catch a false
sentence built from names that all still exist; that is what adversarial review is for.

Lean sources only. Markdown is narrative and historical -- plan.md is *supposed* to
discuss things that were deleted -- so scanning it would need an allowlist, and an
allowlist is how a check like this rots into noise.

Usage:
    lake env lean --run scripts/DumpNames.lean > names.txt
    python3 scripts/check_refs.py names.txt
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TICKED = re.compile(r"`([^`\n]+)`")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*'?$")
SUBSCRIPT = re.compile(r"^[A-Za-z]_[A-Za-z0-9']{1,4}$")

# Namespaces a docstring may elide, being written inside them.
PREFIXES = ["", "Monophilic.", "SimpleGraph.", "SimpleGraph.Monophilic.", "SimpleGraph.ERT."]

# Tactics read like snake_case declarations but are syntax.
TACTICS = {"exact_mod_cast", "push_cast", "norm_num", "norm_cast", "ring_nf",
           "simp_all", "split_ifs", "field_simp", "lean_exe", "permitted_axioms"}
FILE_EXT = (".lean", ".md", ".py", ".sh", ".json", ".toml", ".yml")

# Projections applied to a local hypothesis: nothing global to resolve.
PROJECTIONS = {"mp", "mpr", "symm", "trans", "elim", "intro", "left", "right",
               "fst", "snd", "val", "prop", "out", "choose", "le", "lt", "ne"}


def checkable(tok: str) -> bool:
    """Plausibly a declaration reference, rather than prose or mathematics."""
    if not IDENT.match(tok) or SUBSCRIPT.match(tok) or tok in TACTICS:
        return False
    if tok.endswith(FILE_EXT):
        return False
    parts = tok.split(".")
    if len(parts) > 1 and (parts[-1] in PROJECTIONS or len(parts[0]) <= 2):
        return False
    # Bare words are overwhelmingly English; require a namespace or a snake_case name.
    return "." in tok or "_" in tok


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_refs.py <names.txt>", file=sys.stderr)
        return 2
    known = set(pathlib.Path(sys.argv[1]).read_text().split())
    if len(known) < 1000:
        print(f"::error::name dump looks truncated ({len(known)} names)", file=sys.stderr)
        return 2

    modules = {"Monophilic"} | {"Monophilic." + p.stem for p in ROOT.glob("Monophilic/*.lean")}
    namespaces = {n.rsplit(".", 1)[0] for n in known if "." in n}

    def resolves(t: str) -> bool:
        return (t in modules or t in namespaces
                or any(p + t in known for p in PREFIXES))

    dangling = []
    for path in sorted(ROOT.glob("Monophilic/*.lean")) + [ROOT / "Monophilic.lean"]:
        for lineno, line in enumerate(path.read_text().splitlines(), start=1):
            for tok in (s.strip() for s in TICKED.findall(line)):
                if checkable(tok) and not resolves(tok):
                    dangling.append((path.relative_to(ROOT), lineno, tok))

    if dangling:
        print(f"{len(dangling)} docstring reference(s) name nothing that exists:\n")
        for rel, lineno, tok in dangling:
            print(f"  {rel}:{lineno}: `{tok}`")
        print("\nCheck the surrounding sentence, not just the name: if the declaration was")
        print("deleted, the claim built around it is probably stale too.")
        return 1

    print(f"docstring references all resolve ({len(known)} declarations in scope)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
