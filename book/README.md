# Counting List Colorings — a Verso companion

A textbook companion to the Lean 4 formalization in `../ListColoring/`, covering Kirov & Naimi,
*List coloring and n-monophilic graphs* (Ars Combin. **124** (2016), 329–340; arXiv:1004.5183).

Every displayed statement in the book is an `example` discharged against the corresponding theorem
in the development, so the prose cannot drift from the proofs: rename a theorem or change its
hypotheses and the book stops building.

## Chapters

1. **Counting List Colorings** — why `SimpleGraph.Coloring` is the wrong counting object, the
   `col` / `colConst` / `ECCAt` definitions, renaming invariance, the deletion identity.
2. **Cones over Cliques** — Lemma 1 and complete graphs.
3. **Paths and the Two Recurrences** — paths built by pendant attachment, `A_k` and `B_k`,
   Lemma 3(a).
4. **The Swapping Lemma** — bridges, Lemma 2, Lemma 4.
5. **Minimizing Assignments, and Cycles** — Lemma 3(b), 3(c), and Theorem 1.
6. **What Mechanization Found** — hypotheses that turned out load-bearing, hypotheses that turned
   out unnecessary, and what remains.

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
