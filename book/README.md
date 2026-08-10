# Counting List Colorings — a Verso companion

A textbook companion to the Lean 4 formalization in `../ListColoring/`, covering Kirov & Naimi,
*List coloring and n-monophilic graphs* (Ars Combin. **124** (2016), 329–340; arXiv:1004.5183).

Every displayed statement in the book is an `example` discharged against the corresponding theorem
in the development, so the prose cannot drift from the proofs: rename a theorem or change its
hypotheses and the book stops building.

## Chapters

**Part I** states the results, for a reader who has never met a chromatic polynomial: *Map of the
Formalization*, *Colouring a Graph*, *The Chromatic Polynomial*, *Lists Instead of a Palette*,
*First Answers: Chordal Graphs*, *Theorem 1: Cycles*, *Which Graphs Are 2-Choosable?* (Rubin's
theorem, proved), *Which Graphs Are Enumeratively Chromatic-Choosable at 2?* (Kirov–Naimi's
Theorem 2, unconditional), *Every Graph, Eventually*, and *Reading `Challenge.lean`*.

**Part II** is the proofs: *Counting List Colorings*, *Cones over Cliques* (Lemma 1), *Paths and the
Two Recurrences* (`A_k`, `B_k`, Lemma 3(a)), *The Swapping Lemma* (Lemmas 2 and 4), *Minimizing
Assignments, and Cycles* (Lemmas 3(b), 3(c), Theorem 1), *Cores* (Lemma 5, `K₂,₃`), *Theta Graphs
and Theorem 2*, *Colorable but Not Choosable*, *What Mechanization Found*, and *The Declarations*.

The chapter order is `Book.lean`; each chapter is a module under `Book/`.

## Two checks the build enforces

* **Every displayed statement is an `example`** discharged against a library theorem, so a rename or
  a changed hypothesis breaks the build rather than the prose.
* **Warnings are errors** (`warningAsError` in `lakefile.lean`), and `Book/Reference.lean` carries a
  command that walks every declaration docstring in the library and errors on a backticked name that
  resolves to neither a constant nor a module. Verso does not do this itself: its inline-code
  elaborator falls back to one that ignores elaboration errors, so an unresolvable name renders
  silently.

## Building

```sh
lake build                                                    # elaborates and checks every example
lake env lean --run Main.lean --output _out --depth 2 --without-tex
python3 -m http.server 8000 --directory _out/html-multi       # then open http://localhost:8000
```

Verso's HTML fetches a JSON side-file for code hovers, so opening `index.html` straight from disk
does not work — serve it.

## Notes on the setup

* Verso `v4.32.0`, built from source under this project's `v4.32.2` toolchain.
* This is a **separate Lake project** from the formalization, deliberately: a Verso breakage cannot
  affect the verified development.
* `plausible` pins to the same revision in both Verso and Mathlib, so there is no dependency
  conflict. (During development `.lake/packages` also held symlinks into a sibling Mathlib checkout
  to save disk; that is a local optimisation only, and is `.gitignore`d.)
* **There is deliberately no `lean_exe`.** Linking a native executable that imports Mathlib forces
  compiling all of Mathlib to object code — around 2700 jobs and several GB. Hence the interpreted
  `lake env lean --run` invocation above.
