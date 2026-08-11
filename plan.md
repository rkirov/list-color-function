# Formalizing Kirov–Naimi, *List Coloring and n-Monophilic Graphs*, in Lean 4 / Mathlib

**Target:** machine-checked proofs of the results of R. Kirov & R. Naimi, "List coloring and
$n$-monophilic graphs", Ars Combin. 124 (2016), 329–340 (arXiv:1004.5183).

**Status of the ground:** verified empirically against Mathlib `905b9581` (2026-07-28) — there is
**no** `chromaticPolynomial`, `Choosable`, `listColor`, `IsChordal`, or perfect-elimination-ordering
API. Everything below is built from scratch on top of `SimpleGraph` + `Finset`.

> Correction to `survey.md` §2: it claims Mathlib supplies `SimpleGraph.instFintypeColoring`.
> It does not, at this revision. `G.Coloring α` is a bundled hom type with no `Fintype` instance,
> so it is the wrong counting object; see the design decision in M1.

---

## Design decisions

**D1 — Count over functions, not bundled homs.** Define colorings as a `Finset (V → ℕ)` cut out of
`Fintype.piFinset L` by properness. This is computable, gives `Finset.card` directly, and makes the
list constraint `f v ∈ L v` definitional. `G.Coloring` is used only as a *bridge* for connecting to
Mathlib's `Colorable` / `chromaticNumber`.

**D2 — Colors are `ℕ`, lists are `Finset ℕ`.** Matches the paper (`L : V → Finset ℕ`). The constant
list `[n]` is `Finset.range n` (same cardinality as `{1..n}`; renaming-invariance makes the choice
immaterial — see M1.4).

**D3 — `col G L : ℕ`, not a polynomial.** The paper never needs `P(G,m)` qua polynomial; it needs
the *count*. Polynomiality is a separate (unneeded) theorem. This drops the entire
deletion-contraction/chromatic-polynomial dependency that `survey.md` Stage 1 assumed.

**D0 — The predicate is named for the literature, not for the paper.** Kirov–Naimi's
"`n`-monophilic" did not take hold; the term the literature settled on is *enumeratively
chromatic-choosable* (Kaul et al. 2023; Allred–Mudrock 2025; Chi et al. 2026). The pointwise
predicate is the workhorse — Theorem 1 is "for every `n`", Theorem 2 is at `n = 2` — so it is
`SimpleGraph.ECCAt G n`, with `SimpleGraph.ECC G := ∀ n, G.ECCAt n` alongside it, and every
declaration that used to read `monophilic_…` now reads `ecc_…`. The module namespace and directory
are `ListColoring`, not the name of one predicate. Prose leads with the modern term and keeps
`n`-monophilic as the historical name; `provenance.md` §4 is the record, and the docstrings of
`ListColoring.ecc_two_iff` and `ListColoring.ecc_two_iff_of_rubin` still quote Theorem 2 in the
paper's own words.

**D4 — Chordality via simplicial elimination ordering, not via cycles-have-chords.** Lemma 1 +
induction along an SEO yields Kostochka–Sidorenko immediately. Dirac's theorem (chordal ⟺ SEO) is
the *only* place the cycle-based definition is needed, and it is not required for any Kirov–Naimi
result. Deferred to an optional milestone.

---

## Milestones

| ID | Content | Depends on | Risk |
|----|---------|-----------|------|
| **M0** | Project scaffold, shared Mathlib build | — | ✅ done |
| — | *(status of M1–M9 is in the progress log below; **all of M1–M9 are now done**, M8 unconditionally — Rubin's theorem is proved here — and M9 including the full `H_{n+1}` construction)* | | |
| **M1** | `ListAssignment`, `colorings`, `col`, `ECCAt`; renaming invariance; `Colorable` bridge | M0 | low |
| **M2** | Regime facts: `n < χ(G) ⟹` enumeratively chromatic-choosable; `χ ≤ n < χ_ℓ ⟹` not enumeratively chromatic-choosable; `col` multiplies over components | M1 | low |
| **M3** | **Lemma 1** (adding a simplicial vertex) → **Kostochka–Sidorenko**: SEO ⟹ enumeratively chromatic-choosable at `n` ∀n. Corollaries: complete graphs, trees | M1 | low–med |
| **M4** | **Lemma 2** (list-swap: force `L(v₁) ⊆ L(v₂)`), **Lemma 4** (strict monotonicity in lists on a path) | M1 | med |
| **M5** | **Lemma 3**: `(n,n−1)`-assignments on paths; recurrences `Aₖ=(n−1)Bₖ₋₁`, `Bₖ=Aₖ₋₁+(n−2)Bₖ₋₁`; `Aₖ−Bₖ=(−1)ᵏ`; closed form `Aₖ=((n−1)/n)((n−1)^{k+1}+(−1)ᵏ)`; minimizing ⟹ type A/B | M4 | **high** |
| **M6** | **Theorem 1: every cycle is enumeratively chromatic-choosable at `n` for all n ≥ 2** ← *primary target* | M5 | **high** |
| **M7** | **Lemma 5** (core), **Lemma 6** (K₂,₃ is enumeratively chromatic-choosable at `2`) | M4 | med |
| **M8** | **Theorem 2**: enumeratively chromatic-choosable at `2` ⟺ core is a vertex / a cycle / K₂,₃ / contains an odd cycle | M6, M7, *Rubin* | **blocked** |
| **M9** | **§5**: `H_{n+1}` is `(n+1)`-choosable but not enumeratively chromatic-choosable at `n+1` (Lemmas 7–10) | M1 | high |
| **M10** | *(optional)* Dirac: chordal ⟺ SEO | M3 | med |
| **R** | Verified bibliography, maintained continuously | — | low |
| **B** | Verso textbook companion in `book/` | M1–M6 | ✅ done |

## Progress log

**2026-08-11 — Lean 4.33.0.** Toolchain `v4.32.2 → v4.33.0`, Mathlib `905b9581 → db584cd6`
(*chore: bump toolchain to v4.33.0*), all eight transitive packages to their matching revisions, in
the root, `comparator/` and `book/`. `verify.sh`'s `lean4export` pin moves to the real `v4.33.0`
tag (`15f6055e`); the `comparator` and `nanoda` pins are upstream lean-eval's and are left alone.
Library, comparator workspace and book all build; no `sorry` in `ListColoring/`; the headline
results still depend on exactly the three permitted axioms.

The forcing move was external: `.lake/packages` is a symlink into a sibling checkout, and that
checkout went to 4.33.0 — its Mathlib `.olean`s were rebuilt while its *sources* were still at
v4.32.2, which is what "incompatible header" meant. Repairing it (checking out `db584cd6` and the
eight package revisions the manifest already named) is what made the shared tree consistent again.
No Mathlib rebuild was needed, which matters on a disk with ~5 GB free.

**One Lean change caused essentially all of the breakage: `DecidableRel` became heterogeneous**,
`{α : Sort u} {β : Sort v} → (α → β → Prop) → _`. It is a *reducible* abbreviation for a `Π`-type,
so instance synthesis now unfolds it and introduces the two vertex binders **before** matching — and
by then the binder types have been reduced, `PathV (k+1)` to `Option (PathV k)`. Every
index-recursive instance here (`instDecidableRelPathG`, `…ClosePath`, `…PendantTower`,
`…CliqueTower`, `…Theta`) is offered as a candidate and then fails to resolve, because matching
would mean inverting `PathV`/`TowerV` at an unknown index. Three shapes of fix, by situation:

* **general `k`** — a successor instance with `α` and `β` *ascribed*, e.g.
  `DecidableRel (α := Option (PathV k)) (β := Option (PathV k)) (pathG (k + 1)).Adj`. The binder
  types are then syntactically what the goal already has, so the index is fixed first-order. This is
  possible only because `DecidableRel` is now heterogeneous — the change is its own cure.
* **numeral heights** (`pendantTower _ 2 _`, `theta 3`, `cliqueTower _ 3 _`) — no indexed instance
  can match, since the type is reduced all the way down; the instance is named in a `local instance`
  beside the `#guard` that needs it.
* **`rw`/`simp` that stopped firing** — `rw` matches syntactically and needs the target to be
  type-correct at `implicit` transparency, which fails across the `PathV (k+1)` / `Option (PathV k)`
  boundary, and the instances in the goal are often not the ones the lemma carries. Replaced by
  `exact`/`rfl`/`show`, or by a `have` stating the equation in the local context and rewriting with
  that. Same lesson as the `rw` note in `ListColoring/PathColorable`'s docstring, now biting in more
  places.

**A route that looks right and is not:** making `PathV`/`TowerV` `@[reducible]`. It does fix the
whole `Cycle` file at a stroke — but it defeats the discrimination-tree key `PathV *`, so
`DecidableEq (PathV 6)` and friends stop resolving at numerals, and it changes defeq globally.
Making `pathG`/`pendantTower` reducible is worse still. Both were tried and reverted; the targeted
instances are the smaller change.

Three unrelated Mathlib/Lean drifts, all local: `Finset.card_sdiff` is now the unconditional
`#(t \ s) = #t - #(s ∩ t)` (use `card_sdiff_of_subset`); `simp` no longer strips `Fin.cast` under
`congrArg Fin.val` (go through `Fin.cast_injective` instead); and `simp_all` needs `Subtype.ext_iff`
spelled out for a `Subtype.mk` equality. In `ThetaGen` neither `if_pos`/`if_neg`, `rw`, nor `split`
could select an `ite` branch any more — rewriting the *condition* to `True`/`False` with a named
hypothesis is what works.

**2026-08-08.** M0, M1, M2 complete and machine-checked; no `sorry`, axioms are exactly
`propext, Classical.choice, Quot.sound` throughout.

* `ListColoring/Defs.lean` — `ListAssignment`, `colorings`, `col`, `colConst`, `ECCAt`,
  monotonicity in the lists, positivity.
* `ListColoring/Rename.lean` — `col_image_of_injOn` (renaming colors by any function injective on the
  available colors preserves `col`) and `col_const_eq_colConst` (any `n`-element color set computes
  `col(G,n)`). This licenses the paper's constant "WLOG `L(x) = {1,2}`" moves.
* `ListColoring/Basic.lean` — `Colorable` bridge, `Choosable`, and all three regimes of p. 2:
  `n < χ ⟹` enumeratively chromatic-choosable, `χ ≤ n < χ_ℓ ⟹` not enumeratively chromatic-choosable, `χ ≤ χ_ℓ`. Plus `colFix` and `sum_colFix`.
* `ListColoring/Delete.lean` — **the deletion identity**
  `col(G, M, v, c) = col(G − v, M_c)` and its corollary `col(G,M) = ∑_{c ∈ M v} col(G − v, M_c)`.
  This is the engine of every counting argument in §3. The deleted vertex is `none : Option V`, so
  the graph after deletion lives on `V` itself — no subtypes, no instance transport.
* `ListColoring/Sum.lean` — `col` is multiplicative over disjoint unions, and a disjoint union of
  graphs that are enumeratively chromatic-choosable at `n` is enumeratively chromatic-choosable at `n`.

*Caveat on M2:* "`G` is enumeratively chromatic-choosable iff each component is" is proved in the ⟸ direction over an
explicit disjoint-union decomposition, not over `G.ConnectedComponent` for an abstract `G`. The
paper only ever uses this direction; the abstract version is deferred.

**M3 complete.** `ListColoring/Iso.lean` — `col`, `colConst` and `ECCAt` transfer along a graph
isomorphism. `ListColoring/Cone.lean` — `coneOn G K` (attach a new vertex to `K`), the extension count
`col(coneOn G K, M) = ∑_f |M(none) \ f(K)|`, the exact identity
`colConst(coneOn G K, n) = (n − |K|)·colConst(G, n)` for a clique `K`, and **Lemma 1**. Corollary:
**complete graphs are enumeratively chromatic-choosable at `n` for every `n`**. Note items (1) and (3) turned out not to need
the clique hypothesis, so they are stated for arbitrary `K`.

**M5 half complete.** `ListColoring/Recurrence.lean` — the `A_k`, `B_k` recurrences with
`A_k − B_k = (−1)^k` (eq. 5), both closed forms, and the `min` classification.
`ListColoring/Path.lean` — paths built by attaching a pendant vertex, so that deleting the new vertex
returns the shorter path *definitionally*; `col_pathG_succ` is the peeling recursion.
`ListColoring/PathCount.lean` — **`col_pathAssign`**: the number of colorings of a path of length `k`
from an `(n,n−1)`-assignment is `A_k` (type A) or `B_k` (type B). This is Lemma 3(a).

The proof is the single recursion `inducedList_pathAssign`: colouring the endpoint `c` turns an
`(x,y)`-assignment on `P_{k+1}` into a `(c,y)`-assignment on `P_k`. Type A (`x = y`) never yields
`c = y`, giving `(n−1)` type B terms — eq. (2); type B yields exactly one type A term and `(n−2)`
type B terms — eq. (3).

*Cross-validation:* before proving it, the recurrence (developed independently) and the path graph
(developed independently) were checked against each other numerically — `col(P₁, A) = 2 = A₁`,
`col(P₁, B) = 3 = B₁`, `col(P₂, A) = 6 = A₂`, `col(P₂, B) = 5 = B₂` at `n = 3` — together with
`col(P_k, [n]) = n(n−1)^k`. This confirmed the indexing before any effort went into the induction.

**M4 half complete — Lemma 2 is done.** `ListColoring/Bridge.lean` — `bridge G H v₀ w₀` (disjoint union
plus one edge), `colAvoid`, the decomposition
`col(bridge, M) = ∑_c colFix(G, v₀, c)·colAvoid(H, w₀, c)`, the swap `swapRight`, equation (1) in
additive form, its strict version, and **Lemma 2** proper (`exists_nested_of_bridge`).

Two things the formalization turned up:
* Equation (1) does **not** need `c₂ ∈ L(v₂)`. Only `c₁ ∈ L(v₁)`, `c₁ ∉ L(v₂)`, `c₂ ∉ L(v₁)` are
  used; if `c₂ ∉ L(v₂)` the correction term is `0` and the swap changes nothing. (`c₂ ∈ L(v₂)` *is*
  needed for the measure to drop, i.e. for termination.)
* The iteration needs a case the measure-induction alone does not cover. `|L(v₁) \ L(v₂)|` reaching
  `0` corresponds to `L(v₁) ⊆ L(v₂)`, but the process can also halt via `L(v₂) ⊆ L(v₁)` with the
  measure still positive and *no swap available*. The paper's phrasing ("repeating as long as
  `L(v₁) ⊄ L(v₂)` and `L(v₂) ⊄ L(v₁)`") covers this correctly; a naive induction on the measure does
  not, and the second disjunct has to be produced directly with `L' = L`.

**M4 complete — Lemma 4 done.** `ListColoring/PathColorable.lean` — a path is colorable when one end
has `≥ 1` color and the rest `≥ 2`; any prescribed color at any vertex extends to a full coloring
when all lists have `≥ 2`; and **Lemma 4** (`col_lt_col_of_ssubset`).

**Path splitting done.** `ListColoring/PathSplit.lean` — `pathSplitIso a b : pathG (a+b+1) ≃g
bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)`, plus the counting corollaries. This is what
lets Lemma 2 be applied at an interior edge of a path, as Lemma 3(c) requires. The orientation was
pinned down numerically first: the wrong pairing gives `29` where the truth is `32` at `(a,b)=(2,2)`.

### Engineering note: the `PathV` / `Option` transparency trap

`PathV (k+1)` is *definitionally* `Option (PathV k)` but not syntactically equal to it. Any `rw` or
`simp` whose implicit type argument is `PathV (k+1)` silently fails to match `Option _`, and `rw`
reports "target expression is not type-correct under `instances` transparency". This cost two
separate agents a build round each. **Pattern to follow:** state every inductive step lemma for an
arbitrary graph over `Option V` (e.g. for `G.addPendant v₀`), where `rw` works, and cross into
`PathV (k+1)` only via term-mode `exact`/`refine`, which unify at default transparency.
`ListColoring/PathColorable.lean` and `ListColoring/PathSplit.lean` both follow this.

**Cycles done — half of Theorem 1.** `ListColoring/Cycle.lean` — `closePath k` (the cycle on `k+1`
vertices, `pathG k` plus the edge `pathStart–pathEnd`), the fact that deleting a vertex and fixing
its color leaves a **type A** assignment on the shorter path
(`inducedList_closePath_constList`), and

  `colConst_closePath : (closePath k).colConst (m+2) = (m+2) * pathA m (k-1)`   for `1 ≤ k`,

which is the paper's `col(C, n) = n · A_{k−2}`. Note `1 ≤ k` is the true hypothesis, not `2 ≤ k`:
`closePath 1` is the degenerate single edge and `col = n(n−1) = n·A₀` still holds; `k = 0` genuinely
fails. Verified against the cycle chromatic polynomial `(n−1)^v + (−1)^v (n−1)` at many points.

**What Theorem 1 still needs:** the other half, `col(C, L) ≥ n·A_{k−2}` for a non-constant `L`,
which is where Lemma 3(b)/(c) and the odd/even case split come in, plus the separate `n = 2`
argument via the paper's "forces" relation.

**M5 complete — Lemma 3(a), (b), (c) all proved.** `ListColoring/PathMinimizing.lean` —
`IsPathShape` / `IsNNAssign` predicates, `col_of_isPathShape` (any type A/B-shaped assignment counts
as `A_k`/`B_k`, via renaming), `exists_minimizing`, `nested_of_minimizing`,
`min_pathA_pathB_le_col` (**3(b)**) and `isPathShape_parity_of_minimizing` (**3(c)**).

Two things worth recording:
* **Minimizers exist without any finite-palette detour.** Colors range over all of `ℕ`, so the set
  of candidate assignments is infinite — but one can minimize over the set of *achievable counts*
  `{c | ∃ L', … ∧ col L' = c} ⊆ ℕ` and finish with `Nat.sInf_mem`. Six lines, no relabelling.
* **The "length at least one" in the paper's definition of an `(n,n−1)`-assignment is load-bearing,
  and 3(c) is exactly what needs it.** At `k = 0` the two terminal vertices coincide, every
  `(n,n−1)`-assignment is minimizing (all give `n−1` colorings), and every shape forces `x = y`
  (type A) — while `0` is even, so 3(c) would demand type B. There is a machine-checked witness
  (`not_parity_of_minimizing_length_zero`, at `n = 3`). At `n = 3`, `A₀ = 2` and `B₀ = 1`: the two
  types do not even share a size profile at `k = 0`. Everything is fine from `k = 1` on.
  3(b), by contrast, needs no hypothesis on `k` or `n` at all.
Both now have all their dependencies in place (Lemma 2, path splitting, path colorability); the
remaining work is the canonical-form-up-to-renaming lemma, existence of a minimizer (the colors
range over all of `ℕ`, so this needs a relabelling into a finite palette first), and the
nestedness argument.

**M6 — Theorem 1 proved for `n ≥ 3`.** `ListColoring/CycleECC.lean`:

  `ecc_closePath (hk : 2 ≤ k) (hm : 1 ≤ m) : (closePath k).ECCAt (m + 2)`

covering **every cycle for every `n ≥ 3`**, plus `n = 2` on odd-vertex cycles (vacuous there:
`colConst = 0`). Remaining gap: `n = 2` on even-vertex cycles, the paper's separate "forces"
argument — in progress in `ListColoring/CycleTwo.lean`.

Three things worth recording from the assembly:
* **The odd case needs nothing extra.** For an odd number of vertices, Lemma 3(b) alone gives the
  bound — no non-constancy hypothesis on `L`, no restriction on `n`.
* **The even case's arithmetic is tighter than the obvious sketch.** "One fibre `≥ A+1`, the rest
  `≥ B`" gives only `nA − n + 2 < nA`. The paper's actual Case 2 is stronger: once one fibre falls
  below `A`, it is forced to be *exactly* a type B shape whose palette omits some `c₀`, and `c₀`
  then certifies that every *other* fibre fails to be type B, so all are `≥ A`. Total
  `B + (A+1) + (n−2)A = nA` exactly.
* **No rotation isomorphism was needed.** The paper deletes an edge `vw` with `L(v) ≠ L(w)`, but
  `closePath` can only delete its distinguished vertex. In the deficient case the type B shape
  forces the two neighbours of the deleted vertex to have different lists, which is all the
  argument uses. A genuine simplification of the paper's presentation.

**M7 half complete — Lemma 5 done.** `ListColoring/Core.lean` — a pendant vertex is a cone over a
singleton (`addPendant_eq_coneOn`), the exact pendant counts
`colConst (coneOn G {v}) n = (n−1)·colConst G n` and `col (coneOn G {v}) (extendList L v) = (n−1)·col G L`,
and **both directions** of the pendant step (`ecc_addPendant_iff`). Lemma 5 itself is taken in
*tower* form — `ecc_pendantTower_iff`, for any finite sequence of pendant attachments,
including attachments to previously-added vertices — which is the form the paper actually uses.
"Core" is not defined as a fixpoint of degree-1 deletion over an arbitrary vertex type; the tower is
the reversed deletion sequence.

Two things from it:
* **`2 ≤ n` is a proof artifact, not a real hypothesis.** It is needed to cancel `n−1`, and genuinely
  so — at `n ≤ 1` the cone identity degenerates to `0 ≤ 0` and carries no information. But the
  *conclusion* holds anyway, because `ecc_of_le_one` shows every graph is enumeratively chromatic-choosable at `n` for
  `n ≤ 1`. So the `iff` is stated with no hypothesis on `n` at all.
* A good validation of the tower definition: `pendantTower (pathG 0) 2 … = pathG 2` holds by `rfl` —
  the tower type and the independently-built path type are definitionally identical.

**M7 complete — Lemma 6 done.** `ListColoring/K23.lean` — the product decomposition
`col(K₂,₃, L) = ∑_{a ∈ L(x)} ∑_{b ∈ L(y)} ∏_j |L(zⱼ) \ {a,b}|`, `colConst = 2`, and **Lemma 6**.
The decomposition is proved by fibering colorings over the pair of colours on the small side and
then a bijection from each fibre to a `piFinset`.

*Simplification found:* the paper's first two cases (`Lx = Ly` and `|Lx ∩ Ly| = 1`) **merge**. If any
`p ∈ Lx ∩ Ly` exists and every `L(zⱼ)` contains `p`, then picking *any* `u ∈ Lx \ {p}` and
`v ∈ Ly \ {p}` makes both `(p,p)` and `(u,v)` contribute — covering both cases uniformly, with no
split on `|Lx ∩ Ly|`. Only the disjoint case needs its own argument. Renaming invariance turned out
not to be needed at all.

**M9 foundation done.** `ListColoring/NotChoosable.lean` — `K_{n,nⁿ}` with the large side indexed by
*functions* `Fin n → Fin n`, the separating assignment `L₀`, `col = 0`, hence not `n`-choosable but
`n`-colourable, hence not enumeratively chromatic-choosable at `n`. The `0 < n` hypothesis proved unnecessary (at `n = 0` the
single vertex gets an empty list).

**M9 complete — §5 in full, and the paper's one error.** `ListColoring/Section5.lean` — the graph
`H n p` (`K_{n,p}` with each `vᵢ` joined to every vertex of `n` copies of `K_{n,nⁿ}`), the block
assignment `Lblock`, and Lemmas 7–10: `coloring_v` / `coloring_w` / `col_LH_le` /
`pow_le_colConst` / `not_ecc`, `left_disjoint` / `left_card_eq`, `badColor_unique`, `choosable`.
`exists_choosable_not_ecc` is the theorem for `n ≥ 2`, and
`exists_choosable_not_ecc_of_two_le` is the statement for every list size.

Three things worth recording.

* **The paper's `n ≥ 1` is wrong.** Lemmas 7, 9 and 10 all fail at `n = 1`. `p` is the least
  integer with `nᵖ > x^{n²}`, which at `n = 1` is `1 > 2` — no such `p`, so `H₂` is undefined; and
  for any `p`, `v₁` joins both ends of the single edge of `K_{1,1}`, so `H₂` has a triangle and
  `col(H₂,2) = 0 < 2 = col(H₂,L)`. Lemma 9 fails separately: `K_{1,1}` with both lists `{0,1}` has
  two killing colours. All three are `#guard`s. List size `2` is instead `θ_{2,2,4}`, which this
  development already had from both sides. This is the **first and only** error found in
  Kirov–Naimi; `provenance.md` §3 carries it.
* **Lemma 8 is proved only in the form Lemma 9 consumes** — small-side lists pairwise disjoint,
  each of size exactly `n`. The paper's "`L` is equivalent to `L₀`" needs a colour bijection *and*
  an automorphism, neither of which anything downstream uses. Likewise `col_LH_le` gives the `≤` of
  the paper's `col(H_{n+1},L) = x^{n²}`.
* **A `#guard` that cannot be run.** `#guard f ∈ G.colorings L` unfolds through
  `Finset.decidableMem` to a scan of `Fintype.piFinset L` — `3^29` functions for `H 2 3` — which
  exhausts memory rather than failing. Check the two conjuncts (`∀ x, f x ∈ L x` and
  `G.IsProperColoring f`) instead: same statement, `|V|²` work. `col`/`colConst` are only safe when
  the whole product of list sizes is small, which is why the evaluated checks live at `n = 1` and
  on `K_{2,4}`.

*Arithmetic note:* `a * n + c = b * n + d` with `c, d < n` forcing `a = b ∧ c = d` is **not**
reachable by `omega` — `a * n` is nonlinear with both factors variable. The `Nat.div`/`Nat.mod`
route is the fix.

**M3 complete in general form.** `ListColoring/Chordal.lean` — `cliqueTower` (iterated coning over
cliques, generalizing `pendantTower` from singletons), `IsSimplicial`, and

  `ecc_cliqueTower : G.ECCAt n → ∀ k d, IsSimplicial G k d → (cliqueTower G k d).ECCAt n`

with the corollary over an empty base: **any graph built along a simplicial elimination ordering is
enumeratively chromatic-choosable at `n` for every `n`** — Kostochka–Sidorenko in full. Dirac's theorem is what would connect
this to "chordal" as usually defined and is deliberately not part of the development.

Cross-checks: a pendant tower *is* a clique tower (`pendantTower_eq_cliqueTower`, an honest `Eq` of
graphs), so Lemma 5's forward direction is rederived from this; `ecc_top_fin` is recovered
from the general theorem; and `∀ a b, Adj a b ↔ a ≠ b` on the 2-step tower over `⊥` closes by
`decide`, confirming it really is `K₃`.

**M8 complete — Theorem 2, relative to Rubin.** `ListColoring/Theta.lean` — `θ_{2,2,2m}` built as a
*double cone* `coneOn (coneOn (pathG (2m)) {pathStart, pathEnd}) {…}` (attaching a vertex adjacent to
both branch vertices *is* a path of length 2 between them, so `coneOn` does the work and no new graph
construction is needed), the product formula `col_theta`, the witness assignment, and

  `not_ecc_theta (m) (hm : 2 ≤ m) : ¬ (theta m).ECCAt 2`

via `col = 1 < 2 = colConst`. Then `ecc_two_iff_of_rubin`.

Two boundary facts came out of it. `colConst_theta` holds from `m ≥ 1`, not just `m ≥ 2`. And the
`m ≥ 2` in `not_ecc_theta` is **essential, not an artifact**: `θ_{2,2,2}` *is* `K₂,₃`, where
the same witness gives `col = 2 = colConst` — exactly as it must, since Lemma 6 proves `K₂,₃` is
enumeratively chromatic-choosable at `2`. That the two independent files agree at the boundary is a good check on both.

The quarantine design is worth recording. Rubin's characterization enters as an **explicit
hypothesis**, and the three alternatives are kept as *abstract propositions*
(`CoreIsVertex`, `CoreIsEvenCycle`, `CoreIsTheta m`) rather than being defined. Nothing about cores
can therefore be smuggled in: the only facts used about them are the four enumerative chromatic-choosability inputs, each
of which is proved in this development — trees (Kostochka–Sidorenko), cycles (Theorem 1), `K₂,₃`
(Lemma 6), and `θ_{2,2,2m}` for `m ≥ 2` (this file). The borrowed ingredient is visible in the
statement's own signature and cannot be mistaken for something proved here.

## What the literature actually says about Rubin's hard direction

Read after the `K₂,₄` correction, to stop reconstructing the proof from memory.

**The structural object is the *generalized* theta.** `θ_{k₁,…,k_n}` is two vertices joined by `n`
internally disjoint paths — `n` arbitrary, not `n = 3`. The characterization is that a connected
graph is `2`-choosable iff its core is a single vertex, an even cycle, or `Θ_{2,2,2k}`. This is exactly what the
`K₂,₄` counterexample was pointing at: `K₂,₄` **is** the generalized theta with four paths of
length `2`, so a structural lemma phrased only in terms of ordinary (three-path) thetas can never
see it. The correct structural input is therefore

> connected, minimum degree `≥ 2`, not a cycle ⟹ contains a **generalized** theta (`n ≥ 3`
> internally disjoint paths between two vertices), **or** two cycles meeting in at most one vertex.

with the classification then covering `Θ_{k₁,…,k_n}` for all `n ≥ 3`, not just `n = 3`.

### …and that two-branch statement is *also* false. `K₃,₃ − e` refutes it

**Third structural claim written here, third refutation.** An exhaustive sweep of all bipartite,
2-connected, minimum-degree-`≥ 2`, non-cycle graphs on `≤ 9` vertices — **129,073** of them; only
bipartite matters, since a non-bipartite graph is already killed by its odd cycle — found **4,162**
that satisfy neither branch. The smallest is `K₃,₃` minus an edge, on **six** vertices:

* 8 edges, degree sequence `3,3,2,3,3,2`, 2-connected, bipartite, not a cycle;
* **four** vertices of degree `≥ 3`, whereas a generalized theta has exactly two — so it is not one;
* girth 4, so two cycles meeting in at most one vertex would need `≥ 4 + 4 − 1 = 7` vertices, and
  there are only six — so that branch is unreachable, not merely unused.

Independently re-verified here by brute force over all injective edge-preserving maps. The
best-known member of the 4,162 is the **subdivision of `K₄`** (10 vertices, 12 edges, 4 branch
vertices, 7 cycles, no two of which meet in `≤ 1` vertex), which Rubin's theorem says is not
2-choosable while neither branch reaches it.

**"Contains a generalized theta" was the wrong predicate.** `K₃,₃ − e` contains `θ(1,3,3)` *and*
`θ(2,2,2)`; `K₂,₄` contains only `θ(2,2,2)`. Containing *some* generalized theta says nothing —
what matters is containing a **bad** one.

### The corrected alternative — empirical, not proved

Adding a third branch closes every one of the 129,073 cases:

> connected, minimum degree `≥ 2`, not a cycle ⟹ **is** a generalized theta `Θ(k₁,…,k_n)`,
> **or** contains a **dumbbell** (two cycles joined by a path, meeting in at most one vertex),
> **or** contains a theta `θ(a,b,c)` whose shape is *not* `(2,2,\text{even})`.

Coverage over the sweep: dumbbell 122,494 / bad theta 4,162 / generalized theta 2,417.
`K₃,₃ − e` lands in the middle branch via `θ(1,3,3)`, subdivided `K₄` via `θ(2,4,4)` — both already
proved non-2-choosable by `ListColoring.not_choosable_two_thetaGen`.

**This is an empirical observation from `n ≤ 9`, not a theorem.** Given the track record above,
it should be checked to `n = 10–12` (nauty) and hand-verified *before* any Lean effort is spent on
it. Deciding the correct statement is step 0, and it is not done.

### Why "two cycles meeting in at most one vertex" needs the connecting path

That phrase is *false* as a standalone non-2-choosability criterion: two **disjoint** even cycles
are 2-choosable, since each is and colourings of a disjoint union are independent
(`#guard`: `C₄ ⊔ C₄` has 4 colourings from the constant list `{1,2}`). Connectivity supplies the
path in Rubin's setting, so the proved statement is about the **dumbbell**, with path length `0`
degenerating to the figure-eight. `ListColoring.not_choosable_two_of_dumbbell`.

A pleasant surprise in that proof: **no parity case split is needed.** The forcing chain kills a
prescribed colour at a cycle's base point regardless of the cycle's parity, so there is no
"assume both cycles are even" branch.

### Mathlib has no vertex connectivity at all

Established by whole-tree `grep -w`, not inference. **Zero hits** for `IsKConnected`,
vertex connectivity, cut vertex / articulation, blocks or block-cut trees, biconnectivity, ear
decomposition, Menger, subdivision, topological minor, or graph minor. (`IsBlock` is group actions;
`IsSeparator` is category theory; `IsMinor` is matroids.) Two sections captioned *"results about
2-connected components of a graph, but without naming them"* contain only edge lemmas.

What *does* exist: **edge** connectivity (`IsEdgeConnected`, `IsEdgeReachable`, `IsBridge`), walks
with real surgery (`takeUntil`, `dropUntil`, `rotate`, `bypass`, `toSubgraph`), `IsPath`/`IsCycle`,
girth, `minDegree`/`maxDegree`, `cycleGraph` with `cycleGraph_isContained_iff`, and a rich
`Acyclic.lean`. `Mathlib/Combinatorics/Graph/` is a real multigraph framework but has **no** walks,
cycles, degrees or connectivity, so it cannot carry this either.

**Cost estimate for step 4, from scratch:** `IsTwoConnected` and its API including the Menger-flavoured
"any two vertices lie on a common cycle" (~400–800 lines); Whitney's ear decomposition or the
H-path/fan lemma under it (~600–1200); the branch-vertex decomposition, which is the painful part
because the textbook move — suppress degree-2 vertices to get a multigraph of minimum degree `≥ 3` —
has *no* counterpart here (~600–1500); then the case analysis. **Total ≈ 2,000–4,000 lines of new
Lean**, on top of first establishing a correct structural statement.

### Cheap next step, worth doing regardless

Two small bridges (~150–250 lines) make what already exists composable in Mathlib's own vocabulary:
turn a `c : G.Walk v v` with `c.IsCycle` into the index-sequence form
`not_choosable_two_of_dumbbell` wants (`Walk.getVert`, `Walk.adj_getVert_succ`, `getVert_length`,
`IsCycle.support_nodup`), and show a shortest path between two vertex sets is internally disjoint
from both. Then "connected + two cycles meeting in ≤ 1 vertex ⟹ not 2-choosable" is a corollary.

**The coded `ThetaAlternative` never absorbed this correction, and is false.** `ListColoring.ThetaAlternative`
in `RubinHard.lean` offers only *three-arm* thetas (`thetaGen a b c`), so `K₂,₄` refutes it — the very
graph the paragraph above was written about. Machine-checked, by brute force over all injective
edge-preserving maps out of every candidate:

| disjunct | on `K₂,₄` | how refuted |
|---|---|---|
| is an even cycle | ✗ | degree sequence is `4,4,2,2,2,2`; a cycle is `2`-regular |
| `≃g theta m` | ✗ | `theta m` has maximum degree `3` |
| contains an odd cycle | ✗ | `containsB (cyc 3) = containsB (cyc 5) = false` (bipartite) |
| contains a **bad** `thetaGen a b c` | ✗ | all six valid shapes with `a+b+c ≤ 7` return `false`; only the **good** `θ_{2,2,2}` is present (`true`) |

`a+b+c ≤ 7` is exhaustive because `thetaGen a b c` has `a+b+c-1` vertices and `K₂,₄` has six. So
`ThetaAlternative` must be restated over generalized thetas of arbitrary arity, plus the two-cycle
case, exactly as displayed above. `ThetaClassification` — now **discharged** in `ThetaClass.lean` —
correspondingly needs extending from `thetaGen a b c` to `Θ_{k₁,…,k_n}`.

**This is a defect in the formalization's scaffolding, not in Kirov–Naimi.** The paper cites Rubin's
characterization as known and does not prove it; `ThetaAlternative` is an auxiliary hypothesis
invented here to split Rubin into a structural half and a coloring half.

### The 2026 terminology, and two results that supersede ours

Chi, Lee, Morrissette, Mudrock, Nguyen and Whatley, *Enumeratively Chromatic-Choosable Theta Graphs*
([arXiv:2605.10861](https://arxiv.org/abs/2605.10861), v2, 27 Jun 2026):

* **The name.** `G` is **enumeratively chromatic-choosable** when `P_ℓ(G,m) = P(G,m)` for *every*
  `m ∈ ℕ`. The term was first formally defined in Kaul et al., *Bounding the list color function
  threshold from above*, Involve **16** (2023) 849–882. Note this is the "for all `m`" notion; the
  paper's enumeratively chromatic-choosable at `n` is the **pointwise** one, and the literature gives that no separate name —
  it simply writes `P_ℓ(G,m) = P(G,m)`. The two are not known to coincide: whether
  `P_ℓ(G,m) = P(G,m)` propagates from `m` to `m+1` is **open** (their Question 1, from Kirov–Naimi).
* **Kirov–Naimi is [16]**, and their Theorem 2(iv) — *a connected `G` with `χ(G) = 2` is
  enumeratively chromatic-choosable iff its core is `K₁`, `C_{2k+2}`, or `Θ(2,2,2) = K₂,₃`* — is
  the paper's Theorem 2, attributed to [1, 6, 13, 16, 17].
* **Their Theorem 4** settles all theta graphs: for `Θ(l₁,l₂,l₃)` with `l₁` minimal and `l₂, l₃ ≥ 2`,
  `G` is *not* enumeratively chromatic-choosable iff `l₁, l₂, l₃` all have the same parity and
  `{l₁,l₂,l₃} ≠ {2}`. The proof goes through **DP-coloring**, not list coloring directly.
* **Dong–Zhang, JCTB 161 (2023) 109–119** prove `P_ℓ(G,m) = P(G,m)` for all `m ≥ |E(G)| − 1`. Our
  `ecc_of_two_pow_lt` gives `2^{|E(G)|} < m`, which is exponentially weaker. Wang–Qian–Yan
  [26] is the earlier bound we followed; Dong–Zhang supersedes it.

**A false lead, recorded so it is not chased again.** "Rubin's Block Lemma" — *every 2-connected
graph that is neither complete nor an odd cycle contains an induced even cycle with at most one
chord* — is a **different theorem by the same author**, used for degree-choosability and Brooks-type
results. It is not the route to the `2`-choosability characterization, and its cutset argument does
not specialize to one.

## Specs verified numerically before delegation

Each of the remaining milestones was pinned down by brute-force search *before* any Lean effort was
spent on it. This is cheap and has repeatedly paid for itself.

* **Lemma 6 (K₂,₃).** The decomposition
  `col = ∑_{a ∈ L(x), b ∈ L(y)} ∏_{z} |L(z) \ {a,b}|` was checked against a direct enumeration over
  every 5-tuple of 2-subsets of `{0..4}`: **zero mismatches**. Over the same range the minimum of
  `col` is exactly **2**, confirming Lemma 6, and the case-3 configuration
  `Lx={0,1}, Ly={2,3}, Lu={0,2}, Lv={0,3}, Lw={1,2}` — where three of the four pairs are killed —
  attains it exactly.
* **Theorem 2 (θ-graphs).** A brute-force search over `θ_{2,2,4}` found **48** two-assignments with
  `col = 1 < 2`, confirming the paper's Figure 2 claim. A *uniform* family was then extracted and
  verified at `m = 2,3,4,5`: `u={1,2}`, `w={1,3}`, the two length-2 interior vertices `{1,2}` and
  `{2,3}`, and the long path's interior `{1,2}` repeated `2m−3` times then `{2,3}`, `{1,3}`. A
  uniform family is what a formalization needs; the printed figure covers only `m = 2`.
* **§5 (`K_{n,nⁿ}`).** The assignment giving disjoint blocks to the `A` side and one colour per block
  to each `B` vertex — with `B` indexed by *functions* `Fin n → Fin n` — gives `col = 0` at
  `n = 1,2,3`, while the uniform count is large (`402653202` at `n = 3`). So the failure is genuinely
  a list phenomenon.

## M11 — attempting Rubin's theorem

*A connected graph is `2`-choosable iff its core is a single vertex, an even cycle, or
`θ_{2,2,2m}`.* Currently borrowed as an explicit hypothesis by `ecc_two_iff_of_rubin`.

**Easy direction (the three families are 2-choosable).**
* Even cycles: **essentially free** — `col(C,L) ≥ colConst(C,2) = 2 > 0` straight from Theorem 1.
  Verified to compile in four lines.
* `K₁` / edgeless: trivial.
* `θ_{2,2,2m}`: the real work. The `col_theta` product formula gives a clean reduction — since each
  apex list has two colours, a summand vanishes *only* when that list equals `{g(start), g(end)}`,
  which forces the endpoints to differ. So **if any path colouring identifies the two endpoints the
  summand is immediately nonzero**, and otherwise one needs an achievable endpoint pair distinct
  from both apex lists. The `reach` machinery of `CycleTwo.lean` is exactly the right tool.

**Hard direction (2-choosable ⟹ the core is one of the three).** This is the direction Theorem 2
actually consumes, and it is where the difficulty is. The contrapositive splits as:
* core contains an odd cycle ⟹ not `2`-colourable ⟹ not `2`-choosable — easy;
* core bipartite, min degree `≥ 2`, connected, not a cycle ⟹ it has a vertex of degree `≥ 3` ⟹
  **it contains a theta subgraph** ⟹ that theta is not of the form `(2,2,even)` ⟹ not 2-choosable.

The starred step is the blocker: extracting a theta subgraph needs block/ear-decomposition
machinery that Mathlib does not have, and "follow a path until it returns to the cycle" is a real
induction over walks. Note also that our `theta m` is hardwired as two *length-2* paths, so ruling
out general `θ_{a,b,c}` would need a general theta construction as well.

**Outcome: the easy direction is proved.** `ListColoring/Choosable.lean`, `ThetaChoosable.lean`,
`Rubin.lean`:

* `Choosable.mono` / `Choosable.comap` — choosability passes to subgraphs, on the same vertex type
  and (via `Function.extend`, giving the full palette off the image) on a smaller one;
* `choosable_pendantTower_iff` — the core reduction, mirroring the version for enumerative chromatic-choosability. Unlike that
  one this genuinely needs `2 ≤ n`: at `n ≤ 1` the equivalence is false, since a single vertex is
  `1`-choosable and a single edge is not;
* `choosable_two_closePath_of_odd` — even cycles, four lines from Theorem 1;
* `not_choosable_two_closePath_of_even` — odd cycles are not even `2`-colourable;
* **`choosable_theta`** — `θ_{2,2,2m}` is `2`-choosable;
* `choosable_two_of_rubinFamily` — the three families together.

The `θ` proof came out cleaner than planned. For `|L| = 2` the criterion is a single iff,
`0 < |L \setminus \{g(\text{start}), g(\text{end})\}| \iff L \ne \{g(\text{start}), g(\text{end})\}`,
which subsumes the equal-endpoints case on cardinality grounds — no case split needed at all. The
even-length hypothesis is used *only* in the constant-assignment case.

*A strong cross-check:* `theta 1` **is** `K₂,₃`, and the two files — written independently — were
checked to agree on `col` for **all 243** assignments drawn from three candidate 2-lists, under an
explicit vertex correspondence, as well as on vertex count, edge count and `colConst` at `n = 2,3,4`.

**The loan is now smaller.** Only `rubin.mp` was ever used, so
`ecc_two_iff_of_rubin_hard` takes a one-way implication rather than an `↔`; the old form
survives as a corollary. What is still borrowed reduces to a purely *structural* fact with no
colouring content: a connected graph with minimum degree `≥ 2` that is not a cycle contains a theta
subgraph.

**CORRECTION — the reduction stated above was wrong.** It was claimed here (and reported twice) that
the hard direction reduces to the structural fact *"connected, minimum degree `≥ 2`, not a cycle ⟹
contains a theta subgraph"*. That statement is **false** *and* insufficient. False: the **bowtie**,
two triangles sharing a single vertex, is connected, has minimum degree `2`, is not a cycle, and
contains no theta subgraph at all — both its blocks are cycles. Insufficient even where it holds:
the theta it produces may be a *good* one, and good thetas are `2`-choosable.

**Counterexample: `K₂,₄`** — which this repository already contains, as `SimpleGraph.ERT.K 2`. It is
connected; bipartite, so it has no odd cycle; minimum degree `2`; not a cycle (`6` vertices, `8`
edges); and not any `θ_{2,2,2m}` (it has two vertices of degree `4`). Every theta subgraph of it is
`θ_{2,2,2} = K₂,₃` — three internally disjoint paths between two of its vertices can only be three
of the four length-`2` paths, and between two large-side vertices only two such paths exist — and
`K₂,₃` **is** `2`-choosable. Yet `K₂,₄` is not `2`-choosable (`ERT.not_choosable 2`). All of this is
machine-checked.

So a structural loan strong enough to finish Rubin must also supply *generalized* thetas (four or
more internally disjoint paths) and pairs of cycles meeting in at most one vertex. `ListColoring/
RubinHard.lean` therefore states the structural input as `ThetaAlternative H` — a property *of the
graph at hand* rather than a universal lemma — and documents the gap.

**Not attempted, and why.** The remaining pieces need block or ear decomposition, which Mathlib does
not have, plus a walk induction for "follow a path until it returns to the cycle". The second
obstacle noted earlier is now gone: `thetaGen a b c` gives general theta graphs, and bad shapes are
proved non-`2`-choosable for the whole family `θ_{2,2,odd}` plus `(1,3,3)`, `(3,3,3)`, `(2,4,4)`.

### The one real blocker: M8 needs Rubin's theorem

Theorem 2's converse runs through **Rubin's characterization of 2-choosable graphs** (Erdős–Rubin–
Taylor 1980): a connected graph is 2-choosable iff its core is a single vertex, an even cycle, or
θ_{2,2,2m}. That is a substantial independent formalization, absent from every proof assistant.

Plan: formalize Theorem 2 **relative to Rubin**, i.e. take Rubin's characterization as an explicit
hypothesis, so the Kirov–Naimi contribution is fully verified and the dependency is quarantined and
visible. Formalizing Rubin itself is a separate project, tracked as a stretch goal.

---

## Execution

Sequential where the API contract matters (M1), parallel subagents for independent lemmas once M1 is
frozen. **Invariant: no `sorry` is ever left in `ListColoring/` without being listed in this file.**
Every milestone ends with a clean `lake build` and a `grep -c sorry` check.

The invariant is unchanged by `OpenProblems.lean`, added later: §6's two open questions are stated
and asserted with `sorry` in a **separate `lean_lib`** that imports `ListColoring` and is imported
by nothing, so `ListColoring/` stays clean and no theorem can depend on an unproved statement. CI's
grep is scoped to `ListColoring/` and needs no exception.

## Where the paper stands

| Paper result | Status |
|---|---|
| Lemma 1 (cone over a clique) | ✅ |
| Kostochka–Sidorenko, complete graphs | ✅ |
| Kostochka–Sidorenko, general simplicial elimination ordering | ✅ |
| Lemma 2 (list swap → nested lists) | ✅ |
| Lemma 3(a) (`A_k`, `B_k`, closed forms) | ✅ |
| Lemma 3(b) (`min(A_k,B_k) ≤ col`) | ✅ |
| Lemma 3(c) (minimizer is type A/B by parity) | ✅ |
| Lemma 4 (strict monotonicity on paths) | ✅ |
| **Theorem 1, `n ≥ 3`** | ✅ |
| Theorem 1, `n = 2`, even-vertex cycles | ✅ |
| **Theorem 1 in full — every cycle, every `n ≥ 2`** | ✅ |
| Lemma 5 (cores / pendant towers) | ✅ |
| Lemma 6 (K₂,₃ is enumeratively chromatic-choosable at `2`) | ✅ |
| Theorem 2 (θ-graphs; rest relative to Rubin) | ✅ |
| §5 foundation (`K_{n,nⁿ}` colourable not choosable) | ✅ |
| §5 Lemma 7 (`H_{n+1}` is not `(n+1)`-monophilic) | ✅ |
| §5 Lemma 8 — in the form Lemma 9 consumes, not the full "equivalent to `L₀`" | ✅ |
| §5 Lemma 9, Lemma 10 | ✅ |
| **§5's conclusion at every list size `k ≥ 2`** | ✅ |
| §3 remark: for `n = 2` a minimizing assignment need not be type A/B | not formalized |
| §6 Question 1's negative answer at `n = 2` (`P₂ □ P₃`) | not formalized |

Rubin's characterization of 2-choosable graphs was the one genuine external dependency. It is now
**proved here** (`ListColoring.rubinTheorem`), so Theorem 2 (`ListColoring.ecc_two_iff`) assumes
nothing beyond connectivity. The version taken relative to Rubin survives as
`SimpleGraph.ecc_two_iff_of_rubin` and `ecc_two_iff_of_rubin_hard`.

The full `H_{n+1}` construction of §5 — `n²` copies of `K_{n,nⁿ}` beneath a complete bipartite
`K_{n,p}`, with `p` chosen by a counting argument — is in `ListColoring/Section5.lean`, restricted
to `n ≥ 2` because the paper's `n ≥ 1` is wrong; see the progress log entry and `provenance.md` §3.

### Theorem 1 at `n = 2` — closed

  `ecc_closePath_of_two_le (hk : 2 ≤ k) : (closePath k).ECCAt (m + 2)`

**Every cycle, every `n ≥ 2`, unconditionally.** The `n ≥ 3` half is `CycleECC`; the `n = 2`
half is `CycleTwo` (forcing and propagation) plus `CycleRotate` (the rotation automorphism).

`ListColoring/CycleRotate.lean` supplies what the fixed-edge presentation was missing: `pathIdx` /
`pathVtxEquiv` numbering the cycle by `Fin (k+1)`, an index characterization of adjacency
(`closePath_adj_pathVtx_fin`: adjacent iff `i + 1 = j ∨ j + 1 = i` in `Fin (k+1)`), and
`rotIso : closePath k ≃g closePath k` built from `Equiv.addRight`. That is exactly the freedom the
paper exercises when it *chooses* an edge `vw` with `L(v) ≠ L(w)`.

Three things came out of it, each strengthening what was expected:

* **The conditional hypothesis `H` is provable in a stronger, parity-free form.**
  `two_le_col_closePath_of_not_const` needs only `1 ≤ k` and non-constancy — the
  `L(pathEnd) = L(pathStart)` hypothesis drops out entirely. Only the *constant* case needs `Odd k`.
* **No special-casing of `k = 1`.** The rotation argument runs uniformly for `k ≥ 1`; only `k = 0`
  breaks, and `1 ≤ k` is already available from `Odd k`.
* **The wrap-around edge is never needed to find the differing pair.** If every *path*-consecutive
  pair agreed, `L` would already be constant — so the differing pair can always be taken inside the
  path, at some `i < k`.

*Note on the two earlier failures:* both agents died on **session API limits**, not on the
mathematics, and the first one's 543-line file survived on disk essentially complete. Check the
working tree before concluding an agent produced nothing.

### Historical note: what the gap had been

`ListColoring/CycleTwo.lean` (543 lines) gets almost all the way. Proved there:

* `colConst_closePath_two_of_odd` : `col(C,2) = 2` for a cycle on an even number of vertices, via
  the degenerate `n = 2` case of the recurrences (`A_k, B_k` just alternate `1, 0`);
* `mem_colorings_closePath_iff` / `colorings_closePath_eq_filter` : a cycle colouring is exactly a
  path colouring whose two ends differ — the formal content of "`Q` is the cycle minus one edge";
* `reach k L c` (the colours `pathStart` can take given `c` at `pathEnd`) and
  **`const_of_forall_reach_card_one`, the propagation lemma**: if every colour of `L(pathEnd)`
  forces a colour of `L(pathStart)`, then `L` is constant;
* `exists_reach_eq_pathStart` : hence some colour forces nothing;
* **`two_le_col_closePath_of_ends_ne`** : `2 ≤ col(C,L)` whenever `L(pathEnd) ≠ L(pathStart)` —
  Case 2 of the paper, and it needs no parity hypothesis;
* `col_closePath_const` : the constant case.

**What is left is exactly one configuration**: `L` non-constant with `L(pathEnd) = L(pathStart)`.
`ecc_closePath_two_of_odd` is stated conditionally on it, so the gap is quarantined in a
hypothesis rather than hidden.

That configuration is precisely where the paper *chooses a different edge* `vw` with `L(v) ≠ L(w)`
and deletes that one. `closePath` can only delete its distinguished edge, so closing it needs a
**rotation automorphism** of the cycle — `ListColoring/CycleRotate.lean`, in progress. All the
ingredients exist: `pathVtx` with `pathVtx_inj` and `exists_pathVtx`, `closePath_adj`, and
Mathlib's `finRotate`.

*Note on the two failed attempts:* both agents died on **session API limits**, not on the
mathematics — and the first one's work survived on disk and turned out to be nearly complete. Worth
remembering: check the working tree before concluding an agent produced nothing.

What is known about it, so the next attempt starts ahead:

* **There is no shortcut.** One might hope non-constant assignments give strictly more colourings,
  reducing everything to the constant case. That is false — exhaustively, **72** non-constant
  2-assignments on `C₄` and **720** on `C₆` achieve exactly the minimum of `2`. The paper says as
  much (every even cycle has a non-constant minimizing 2-assignment). The forcing argument is
  necessary.
* **The setup is favourable.** `closePath j` is `pathG j` plus the single `pathStart`–`pathEnd`
  edge, so the paper's path `Q` (cycle minus one edge, keeping vertices) is *literally* `pathG j`
  with `v = pathEnd`, `w = pathStart`. **No rotation isomorphism is needed** — the propagation step
  works from this fixed edge because `Q`'s vertices are all of the cycle's.
* The constant-`L` case is a one-liner from `col_const_eq_colConst`; the work is entirely in the
  forcing/propagation argument and the final four-way case split (paper pp. 5–6).
* Odd-vertex cycles at `n = 2` *are* covered and are vacuous (`colConst = 0`).

## The Verso companion (`book/`)

`book/` is a **separate Lake project** holding a Verso textbook companion, *Counting List
Colorings*. It is deliberately separate so that a Verso breakage cannot affect the verified
development. Six chapters — Counting, Cones over Cliques, Paths and the Two Recurrences, The
Swapping Lemma, Minimizing Assignments and Cycles, What Mechanization Found — plus a checked
bibliography.

**Every displayed statement in the book is an `example` discharged against the real theorem**, so
the prose cannot drift from the development: if a theorem is renamed or its hypotheses change, the
book stops building.

Build notes:

* Verso `v4.33.0` (its own toolchain is `v4.33.0`, matching ours).
* `book/.lake/packages` holds symlinks to the shared Mathlib chain plus real clones of `verso`,
  `subverso`, `MD4Lean`, `illuminate` (~43 MB). `plausible` pins to the *same* rev in Verso and
  Mathlib, so there is no dependency conflict.
* **There is deliberately no `lean_exe`.** Linking a native executable that imports Mathlib forces
  compilation of all of Mathlib to object code — ~2700 jobs and several GB, which this disk does not
  have. Generate the HTML through the interpreter instead:
  `cd book && lake env lean --run Main.lean`
* `Article` in Verso's bibliography has a *required* `month` field (no default), unlike `pages` and
  `url`.

## Notes on the build

Disk is at 94% (5.2 GB free); a second Mathlib checkout does not fit. `.lake/packages` is a symlink
to a sibling Mathlib checkout's `.lake/packages` (same toolchain `v4.32.2`, same rev `905b9581`), so the
prebuilt Mathlib is shared read-only. Full build: ~12 s.

---

## The plan for Rubin's theorem, from the primary source

**Source found.** The original is online at Erdős's own archive:
[users.renyi.hu/~p_erdos/1980-07.pdf](https://users.renyi.hu/~p_erdos/1980-07.pdf) — P. Erdős,
A. L. Rubin, H. Taylor, *Choosability in graphs*, Congr. Numer. **26** (1980), 125–157. The
characterization is on pp. 131–134 under "CHARACTERIZATION OF 2-CHOOSABLE GRAPHS", with Rubin's
proof given in full.

Two negative findings first, so nobody re-treads them. **Zhu (EJC 2009) does not prove it** — he
states it as his Theorem 14 with citation [6] and *reduces to it*: "since every on-line 2-choosable
graph is 2-choosable, to prove that all the other graphs are not on-line 2-choosable, it suffices to
show that `θ₂,₂,₂ₙ` is not on-line 2-choosable". Likewise Chi et al. 2026 and Allred–Mudrock 2025
cite it only.

### The headline: **the proof needs no ear decomposition, no Menger, and no 2-connectivity**

This overturns the ≈2,000–4,000-line estimate recorded above. Rubin never introduces
2-connectivity. He works directly with the core (minimum degree `≥ 2`) and disposes of the
non-2-connected case *as two of his five types*. The whole argument runs on a **shortest cycle** and
two **shortest connecting paths**, with a six-way case analysis on where the second one lands.

### Rubin's five types, verbatim

> either `G` is in `T`, or else `G` contains a subgraph belonging to one of the following five types.
> 1. An odd cycle.
> 2. Two node disjoint even cycles connected by a path.
> 3. Two even cycles having exactly one node in common.
> 4. `θ_{a,b,c}` where `a ≠ 2` and `b ≠ 2`.
> 5. *(shown as a figure; from case (v) it is the generalized theta on four arms, `K₂,₄`-like)*

where `T = {K₁, C_{2m+2}, θ_{2,2,2m} : m ≥ 1}`.

**All five are already proved non-2-choosable in this library.** That half of the work is done:

| Rubin's type | our theorem |
|---|---|
| 1. odd cycle | `not_choosable_two_of_contains_odd_cycle` |
| 2. two disjoint even cycles joined by a path | `not_choosable_two_of_dumbbell` |
| 3. two even cycles sharing one node | `not_choosable_two_of_figureEight` |
| 4. `θ_{a,b,c}`, `a ≠ 2 ≠ b` | `not_choosable_two_thetaGen` / `choosable_two_gtheta_iff` |
| 5. generalized theta on `≥ 4` arms | `not_choosable_two_gtheta_of_four` |

(Type 4 looks narrower than our "bad shape", but it is not a gap: `θ_{2,2,c}` with `c` odd contains
a cycle of odd length `2 + c`, so it is already type 1.)

Rubin also gives a *merge reduction* for types 2–5 — delete a node `b` and merge its neighbours,
which preserves non-2-choosability because the graph stays bipartite, so no loops appear — reducing
each type to one of four small graphs checked by hand. **We do not need it**, having proved each
type directly. Worth recording that he flags it as special: "this proof would not have worked for
3-choosability."

### What is actually left: the extraction

Only the structural half. Rubin's argument, step by step:

1. If `G` has an odd cycle → **type 1**. So assume `G` is **bipartite**.
2. Let `C₁` be a **shortest cycle**. Some edge of `G` is not in `C₁`, else `G` is an even cycle and
   so in `T`.
3. If some cycle `C₂` meets `C₁` in at most one node → **type 2 or 3**.
4. Otherwise let `P₁` be a **shortest path, edge-disjoint from `C₁`, joining two distinct nodes of
   `C₁`** — known to exist by step 3. If `C₁ ∪ P₁ ∉ T` → **type 4**.
5. Otherwise `C₁ ∪ P₁ = θ_{2,2,2m}` and `C₁` is a **4-cycle**. There must be more to `G`, so let
   `P₂` be a shortest path edge-disjoint from `C₁ ∪ P₁` joining two distinct nodes of `C₁ ∪ P₁`.
6. **Six cases** on the ends of `P₂`, against the labelled nodes `a, b, a', b'` of `C₁`:
   (i) two interior nodes of `P₁` → a cycle disjoint from `C₁`, **type 2**;
   (ii) `a` and an interior node of `P₁` → cycle meeting `C₁` once, **type 3**;
   (iii) `b` and an interior node of `P₁` → **type 4**;
   (iv) `a` and `b` → **type 4**;
   (v) `a` and `a'`: if `|P₁| = 2` → **type 5**, else → **type 4**;
   (vi) `b` and `b'` → delete any edge of `C₁` to expose a `θ`, **type 4**.

### Revised cost, and what to build

Everything here is finite case analysis over walks, which Mathlib *does* support
(`Walk`, `IsCycle`, `takeUntil`, `dropUntil`, `rotate`, `bypass`, `girth`). The estimate drops from
2,000–4,000 lines to roughly **800–1,500**, and the risky dependencies vanish. New pieces needed:

* **E1.** Minimum degree `≥ 2` ⟹ a cycle exists; and a *shortest* cycle exists (Mathlib has `girth`
  and `exists_girth_eq_length` — likely most of this).
* **E2.** The existence claim in step 4: if no cycle meets `C₁` in `≤ 1` node, and `G` is connected
  with an edge outside `C₁`, then some path edge-disjoint from `C₁` joins two distinct nodes of
  `C₁`. **This is the one genuinely new piece of graph theory**, and it is where the effort should
  go first — it is also the step most likely to hide a subtlety, given this project's record with
  structural claims.
* **E3.** The `Walk`-to-index bridge already identified as cheap (~150–250 lines): turn a
  `c : G.Walk v v` with `c.IsCycle` into the `(A, m)` index form that
  `not_choosable_two_of_dumbbell` consumes.
* **E4.** The six-case analysis of step 6, and assembly.

**Do E3 first** — it is cheap, unblocks types 2 and 3 in Mathlib's own vocabulary, and is useful
regardless. Then E2, alone, brute-force checked before any proof. Then E1 and E4.

**Before writing any Lean for E2 and E4, machine-check the case analysis** on all bipartite
minimum-degree-`≥ 2` graphs up to 9 or 10 vertices: for each, confirm that the type Rubin's
procedure lands on really is one of the five and really contains the claimed subgraph. Three
structural claims written from memory in this project have been refuted by graphs on 6–7 vertices;
this one comes from the primary source, but it should still be checked before it is trusted.
