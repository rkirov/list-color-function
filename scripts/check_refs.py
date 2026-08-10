#!/usr/bin/env python3
"""Catch prose that outlived the code it described.

The Lean kernel checks theorem *statements*. It checks nothing inside a docstring, a
markdown table, or a README claim. So when a declaration is deleted or renamed, every
backticked reference to it in prose silently becomes a lie — and that is exactly how a
false claim about `ThetaAlternative` survived the deletion of `ThetaAlternative` itself.

This script cross-references every backticked Lean identifier in the docstrings and the
markdown against the real environment, and fails if one does not resolve.

Usage:
    lake env lean --run scripts/DumpNames.lean > names.txt
    python3 scripts/check_refs.py names.txt
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# Backticked spans in docstrings, comments and markdown.
TICKED = re.compile(r"`([^`\n]+)`")
# A plausible Lean identifier: letters/digits/underscore/prime, dot-separated.
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*'?$")

# Namespaces a docstring may elide, since it is written inside them.
PREFIXES = ["", "Monophilic.", "SimpleGraph.", "SimpleGraph.Monophilic.",
            "Monophilic.SimpleGraph.", "SimpleGraph.ERT.", "Monophilic.ERT."]

# Prose words that happen to match the identifier shape. Extend deliberately; every
# entry here is a hole in the check, so prefer being specific over being broad.
IGNORE = {
    "sorry", "admit", "native_decide", "decide", "rfl", "simp", "omega", "rw", "exact",
    "refine", "show", "have", "let", "fun", "by", "at", "with", "in", "do", "match",
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "namespace", "end",
    "example", "variable", "open", "import", "attribute", "deriving", "where", "this",
    "true", "false", "True", "False", "Prop", "Type", "Sort", "n", "m", "k", "G", "H",
    "L", "V", "W", "a", "b", "c", "d", "v", "w", "x", "y", "z", "i", "j", "t", "p", "q",
    "f", "g", "e", "s", "N", "P", "A", "B", "C", "M", "T", "Adj", "TODO", "iff", "ne",
    "lake", "cache", "get", "build", "main", "test", "lint", "true_", "id",
    # tactic names, which read like declarations but are syntax
    "exact_mod_cast", "push_cast", "norm_num", "norm_cast", "ring_nf", "simp_all",
    "field_simp", "split_ifs", "omega_nat", "decide_eq", "aesop_graph", "gcongr",
    # build- and tooling-config keys, not Lean declarations
    "lean_exe", "lean_lib", "permitted_axioms", "theorem_names", "definition_names",
    "packagesDir", "mathlib4_docs", "use_mathlib_cache", "lake_package_directory",
}


# `A_k`, `B_j`, `M_c`, `v_i`, `P_ℓ` — subscripted mathematics, not declarations.
SUBSCRIPT = re.compile(r"^[A-Za-z]_[A-Za-z0-9']{1,4}$")


def looks_like_a_name(tok: str) -> bool:
    """Only check tokens that are plausibly declaration references.

    Requires a dot or an underscore: bare single words in prose are overwhelmingly
    English, and checking them produces noise that would get the whole check ignored.

    Three shapes are excluded because they resolve against something other than the
    constant table, and flagging them would drown the real findings:
      * subscripted mathematics (`A_k`);
      * field access on a local (`d.IsSimplicial`, `e.symm`) — the head is a bound
        variable, so there is nothing global to check it against;
      * module and namespace names, handled by the caller, which knows the file layout.
    """
    if tok in IGNORE or not IDENT.match(tok):
        return False
    if any(tok.endswith(ext) for ext in (".lean", ".md", ".py", ".sh", ".json", ".toml",
                                         ".yml", ".html", ".svg")):
        return False
    if SUBSCRIPT.match(tok):
        return False
    if tok.rsplit(".", 1)[-1] in {"com", "ca", "org", "net", "edu", "io", "gov", "uk"}:
        return False
    # `h.mp`, `rubin.mpr`, `e.symm` -- a projection applied to a local hypothesis.
    if "." in tok and tok.rsplit(".", 1)[-1] in {
            "mp", "mpr", "symm", "trans", "elim", "intro", "left", "right", "fst",
            "snd", "val", "prop", "out", "choose", "le", "lt", "ne", "some"}:
        return False
    head = tok.split(".")[0]
    if "." in tok and len(head) <= 2:
        return False
    return "." in tok or "_" in tok


def resolvable(tok: str, known: set[str], modules: set[str], namespaces: set[str]) -> bool:
    """A reference is fine if it names a declaration, a module, or a namespace."""
    if tok in modules or tok in namespaces:
        return True
    return any(p + tok in known for p in PREFIXES)


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_refs.py <names.txt>", file=sys.stderr)
        return 2
    known = set(pathlib.Path(sys.argv[1]).read_text().split())
    if len(known) < 1000:
        print(f"::error::name dump looks truncated ({len(known)} names)", file=sys.stderr)
        return 2

    # Module names are legitimate references but are not constants.
    modules = {"Monophilic", "Book"}
    for p in ROOT.glob("Monophilic/*.lean"):
        modules.add("Monophilic." + p.stem)
    for p in ROOT.glob("book/Book/*.lean"):
        modules.add("Book." + p.stem)

    # Namespaces likewise: a prefix under which some constant lives.
    namespaces = {n.rsplit(".", 1)[0] for n in known if "." in n}

    # Deliberate references to declarations that no longer exist -- historical notes
    # recording something that was deleted, and why. Every entry needs a reason, so that
    # the allowlist stays an audit trail rather than a place to hide breakage.
    allow: set[str] = set()
    allow_file = ROOT / "scripts" / "refs-allow.txt"
    if allow_file.exists():
        for raw in allow_file.read_text().splitlines():
            entry = raw.split("#", 1)[0].strip()
            if entry:
                allow.add(entry)

    # survey.md is excluded on purpose: it is the pre-project scoping report, preserved
    # as written. Several of its guesses about Mathlib turned out to be wrong -- that is
    # part of the record, and correcting it would destroy the history.
    targets = sorted(ROOT.glob("Monophilic/*.lean")) + [ROOT / "Monophilic.lean"] + \
        [p for p in sorted(ROOT.glob("*.md")) if p.name != "survey.md"] + \
        sorted(ROOT.glob("book/Book/*.lean"))

    dangling: list[tuple[str, int, str]] = []
    for path in targets:
        if not path.exists():
            continue
        for lineno, line in enumerate(path.read_text().splitlines(), start=1):
            for span in TICKED.findall(line):
                tok = span.strip()
                if not looks_like_a_name(tok):
                    continue
                rel = str(path.relative_to(ROOT))
                if f"{rel}:{tok}" in allow:
                    continue
                if not resolvable(tok, known, modules, namespaces):
                    dangling.append((rel, lineno, tok))

    if dangling:
        print(f"{len(dangling)} backticked reference(s) do not resolve:\n")
        for rel, lineno, tok in dangling:
            print(f"  {rel}:{lineno}: `{tok}`")
        print("\nEach is prose referring to a declaration that does not exist. Either the")
        print("name is wrong, or the declaration was deleted and the claim around it is")
        print("now unsupported -- check the surrounding sentence, not just the name.")
        print("If the reference is deliberate (a note about something deleted), add")
        print("\"<path>:<name>\" to scripts/refs-allow.txt with a reason.")
        return 1

    print(f"all backticked references resolve ({len(known)} declarations in scope)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
