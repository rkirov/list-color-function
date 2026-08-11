/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Cone
import ListColoring.PathCount

/-!
# Theta graphs are not enumeratively chromatic-choosable at `2`

Kirov–Naimi's Theorem 2 characterizes the graphs that are enumeratively chromatic-choosable at `2`.
Its converse runs through **Rubin's theorem** (Erdős–Rubin–Taylor 1980): a connected graph is
`2`-choosable iff its core is a single vertex, an even cycle, or `θ_{2,2,2m}`. Rubin's theorem is
*not* proved here (it is not available in any proof assistant); what this file supplies is the one
remaining graph-theoretic input, namely that the last family in Rubin's list is enumeratively
chromatic-choosable at `2` only in its first member:

> for `m ≥ 2`, `θ_{2,2,2m}` is **not** enumeratively chromatic-choosable at `2`.

(For `m = 1` the graph `θ_{2,2,2}` is `K₂,₃`, which *is* enumeratively chromatic-choosable at `2`;
that is Lemma 6.)

## The construction

`θ_{2,2,2m}` consists of two branch vertices joined by three internally disjoint paths of lengths
`2`, `2` and `2m`. A new vertex joined to both branch vertices *is* a path of length two between
them, so the graph is obtained from `pathG (2m)` by coning twice over its pair of terminal
vertices — see `ListColoring.theta`. That pair is not a clique, so `colConst_coneOn` does not apply,
but `col_coneOn` needs no clique hypothesis and iterating it gives the product formula
`ListColoring.col_theta`.

## The witness

`ListColoring.thetaWitness` gives the lists `{1,2}` and `{2,3}` to the two added vertices, `{1,2}`
to `pathEnd`, `{1,3}` to `pathStart`, and along the long path, read from the `pathEnd` side, `{1,2}`
repeated `2m-3` times, then `{2,3}`, then `{1,3}` (this is `ListColoring.lvl`, indexed by the
distance to `pathStart`). Peeling the two apexes (`col_thetaOf_thetaAssign`) leaves four terms, and
in three of them a terminal vertex of the long path is left with an empty list or the forced
alternating chain `1, 2, 1, 2, …` arrives at the far end with its only remaining color already used.
The fourth term contributes `1`, whereas `col(θ_{2,2,2m}, 2) = 2`.

## Main definitions

* `ListColoring.theta m` : the theta graph `θ_{2,2,2m}`
* `ListColoring.levelAssign` : a list assignment on a path given by a level function, with the two
  terminal lists overridden
* `ListColoring.thetaWitness m` : the witness `2`-list assignment

## Main results

* `SimpleGraph.sum_comp_some_coneOn` : a weighted version of `col_coneOn`
* `SimpleGraph.col_coneOn_optAssign` : peeling the apex of a cone
* `ListColoring.col_theta` : **the product formula** for `col(θ_{2,2,2m}, M)`
* `ListColoring.colConst_theta` : `col(θ_{2,2,2m}, 2) = 2` for `m ≥ 1`
* `ListColoring.col_theta_witness` : `col(θ_{2,2,2m}, L) = 1` for the witness `L`, when `m ≥ 2`
* `ListColoring.not_ecc_theta` : **`θ_{2,2,2m}` is not enumeratively chromatic-choosable at `2` for
  `m ≥ 2`**
* `SimpleGraph.ecc_two_iff_of_rubin` : **Theorem 2**, stated relative to Rubin's theorem,
  which appears as an explicit hypothesis
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {K : Finset V}

/-- An empty list at some vertex kills all colorings. -/
lemma col_eq_zero_of_empty {L : ListAssignment V} (v : V) (h : L v = ∅) : G.col L = 0 := by
  rw [col_eq_zero_iff]
  intro f hf
  exact absurd (hf v) (by simp [h])

/-- The list assignment on `Option V` giving the list `x` to the apex `none`. -/
def optAssign {V : Type*} (x : Finset ℕ) (P : ListAssignment V) : ListAssignment (Option V) :=
  fun v => match v with
    | none => x
    | some w => P w

@[simp] lemma optAssign_none {V : Type*} (x : Finset ℕ) (P : ListAssignment V) :
    optAssign x P none = x := rfl

@[simp] lemma optAssign_some {V : Type*} (x : Finset ℕ) (P : ListAssignment V) (w : V) :
    optAssign x P (some w) = P w := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Deleting the apex of a cone gives back the graph that was coned off. -/
@[simp] lemma delNone_coneOn : (coneOn G K).delNone = G := rfl

omit [Fintype V] in
/-- The list assignment induced on `G` by giving the color `c` to the apex of `coneOn G K`:
exactly the vertices of `K` lose the color `c`. -/
lemma inducedList_coneOn (M : ListAssignment (Option V)) (c : ℕ) (v : V) :
    (coneOn G K).inducedList M c v = if v ∈ K then (M (some v)).erase c else M (some v) := rfl

/-- **Weighted extension count.** A weighted version of `SimpleGraph.col_coneOn`: summing any
weight that depends only on the restriction of a coloring to the old vertices, the apex
contributes the factor `|M(none) \ f(K)|` computed in `card_filter_comp_some`. -/
theorem sum_comp_some_coneOn (M : ListAssignment (Option V)) (φ : (V → ℕ) → ℕ) :
    ∑ F ∈ (coneOn G K).colorings M, φ (F ∘ some)
      = ∑ g ∈ G.colorings (M ∘ some), (M none \ K.image g).card * φ g := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun _ hF => comp_some_mem_colorings hF)
    (fun F => φ (F ∘ some))]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hconst : ∀ F ∈ ((coneOn G K).colorings M).filter (fun F => F ∘ some = g),
      φ (F ∘ some) = φ g := fun F hF => by rw [(Finset.mem_filter.mp hF).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, card_filter_comp_some hg]

/-- **Peeling the apex of a cone.** Summing over the color given to the apex, the vertices of `K`
lose that color. -/
theorem col_coneOn_optAssign (x : Finset ℕ) (P : ListAssignment V) :
    (coneOn G K).col (optAssign x P)
      = ∑ c ∈ x, G.col (fun v => if v ∈ K then (P v).erase c else P v) := by
  refine (col_eq_sum_delNone (coneOn G K) (optAssign x P)).trans ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  show G.col _ = G.col _
  congr 1

end SimpleGraph

namespace ListColoring

open SimpleGraph

/-- `pathG k` with a new vertex joined to both of its terminal vertices. -/
def thetaBaseOf (k : ℕ) : SimpleGraph (Option (PathV k)) :=
  coneOn (pathG k) {pathStart k, pathEnd k}

instance instDecidableRelThetaBaseOf (k : ℕ) : DecidableRel (thetaBaseOf k).Adj :=
  inferInstanceAs (DecidableRel (coneOn (pathG k) {pathStart k, pathEnd k}).Adj)

/-- `pathG k` with two new vertices, each joined to both terminal vertices of the path. -/
def thetaOf (k : ℕ) : SimpleGraph (Option (Option (PathV k))) :=
  coneOn (thetaBaseOf k) {some (pathStart k), some (pathEnd k)}

instance instDecidableRelThetaOf (k : ℕ) : DecidableRel (thetaOf k).Adj :=
  inferInstanceAs
    (DecidableRel (coneOn (thetaBaseOf k) {some (pathStart k), some (pathEnd k)}).Adj)

/-- The vertex type of `θ_{2,2,2m}`. -/
abbrev ThetaV (m : ℕ) : Type := Option (Option (PathV (2 * m)))

/-- The theta graph `θ_{2,2,2m}`. -/
def theta (m : ℕ) : SimpleGraph (ThetaV m) := thetaOf (2 * m)

instance instDecidableRelTheta (m : ℕ) : DecidableRel (theta m).Adj :=
  inferInstanceAs (DecidableRel (thetaOf (2 * m)).Adj)

/-! ### Numerical checks on the construction

`θ_{2,2,4}` has `2m + 1 + 2 = 7` vertices and `2m + 4 = 8` edges, and being bipartite and
connected it has exactly two colorings from a constant list of two colors. -/

-- At a *numeral* height the vertex type reduces past anything `instDecidableRelTheta` can match
-- (it would have to invert `2 * ?m`), so the instances the `#guard`s below need are named here.
-- See `ListColoring.instDecidableRelPathGSucc` for the general story.
local instance : DecidableRel (theta 2).Adj := instDecidableRelTheta 2
local instance : DecidableRel (theta 3).Adj := instDecidableRelTheta 3
local instance : DecidableRel (theta 4).Adj := instDecidableRelTheta 4
local instance : DecidableRel (theta 5).Adj := instDecidableRelTheta 5

#guard Fintype.card (ThetaV 2) = 7
#guard (theta 2).edgeFinset.card = 8
#guard (theta 3).edgeFinset.card = 10
#guard (theta 2).colConst 2 = 2
#guard (theta 3).colConst 2 = 2

/-- The lists along the long path, indexed by the distance to `pathStart` (so index `k` is the
list of `pathEnd k`). -/
def lvl : ℕ → Finset ℕ
  | 0 => {1, 3}
  | 1 => {1, 3}
  | 2 => {2, 3}
  | _ + 3 => {1, 2}

/-- A list assignment on `pathG k` given by a level function `Λ`, with the list at `pathEnd`
overridden to `h` and the list at `pathStart` overridden to `s`. -/
def levelAssign : (k : ℕ) → (ℕ → Finset ℕ) → Finset ℕ → Finset ℕ → ListAssignment (PathV k)
  | 0, _, _, s => fun _ => s
  | k + 1, Λ, h, s => fun v =>
      match v with
      | none => h
      | some w => levelAssign k Λ (Λ k) s w

/-- A list assignment on `thetaOf k`: `Lb` at the outer apex, `La` at the inner apex, and `P`
along the long path. -/
def thetaAssign (k : ℕ) (Lb La : Finset ℕ) (P : ListAssignment (PathV k)) :
    ListAssignment (Option (Option (PathV k))) := optAssign Lb (optAssign La P)

/-- Erasing the color `c` from the lists of both terminal vertices of a path. -/
def eraseEnds (k : ℕ) (c : ℕ) (P : ListAssignment (PathV k)) : ListAssignment (PathV k) :=
  fun w => if w ∈ ({pathStart k, pathEnd k} : Finset (PathV k)) then (P w).erase c else P w

/-- The witness `2`-list assignment on `θ_{2,2,2m}`. -/
def thetaWitness (m : ℕ) : ListAssignment (ThetaV m) :=
  thetaAssign (2 * m) {2, 3} {1, 2} (levelAssign (2 * m) lvl {1, 2} {1, 3})

/-! ### Numerical checks on the witness -/

#guard (theta 2).col (thetaWitness 2) = 1
#guard (theta 3).col (thetaWitness 3) = 1
#guard (theta 4).col (thetaWitness 4) = 1
#guard (theta 5).col (thetaWitness 5) = 1
#guard (theta 4).colConst 2 = 2
#guard (theta 5).colConst 2 = 2
#guard ∀ v ∈ (univ : Finset (ThetaV 3)), (thetaWitness 3 v).card = 2

-- `θ_{2,2,2}` is `K₂,₃` (five vertices, six edges), and there the witness does *not* beat the
-- constant list: `K₂,₃` is enumeratively chromatic-choosable at `2` (Lemma 6). The hypothesis
-- `m ≥ 2` is not an artifact.
#guard Fintype.card (ThetaV 1) = 5
#guard (theta 1).edgeFinset.card = 6
#guard (theta 1).col (thetaWitness 1) = 2
#guard (theta 1).colConst 2 = 2

/-! ### The product formula -/

/-- **The product formula for a theta graph.** Iterating `SimpleGraph.col_coneOn` (which needs no
clique hypothesis) expresses the number of colorings of `thetaOf k` as a sum over the colorings of
the long path, each contributing the product of the numbers of colors left at the two apexes. -/
theorem col_thetaOf (k : ℕ) (M : ListAssignment (Option (Option (PathV k)))) :
    (thetaOf k).col M
      = ∑ g ∈ (pathG k).colorings (fun v => M (some (some v))),
          (M (some none) \ {g (pathStart k), g (pathEnd k)}).card
            * (M none \ {g (pathStart k), g (pathEnd k)}).card := by
  have step1 : (thetaOf k).col M
      = ∑ F ∈ (coneOn (pathG k) {pathStart k, pathEnd k}).colorings (M ∘ some),
          (M none \ {(F ∘ some) (pathStart k), (F ∘ some) (pathEnd k)}).card := by
    show (coneOn (thetaBaseOf k) {some (pathStart k), some (pathEnd k)}).col M = _
    rw [col_coneOn]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [Finset.image_insert, Finset.image_singleton]
    rfl
  refine step1.trans ((sum_comp_some_coneOn (M ∘ some)
    (fun g => (M none \ ({g (pathStart k), g (pathEnd k)} : Finset ℕ)).card)).trans ?_)
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.image_insert, Finset.image_singleton]
  rfl

/-- **The product formula for `θ_{2,2,2m}`.** -/
theorem col_theta (m : ℕ) (M : ListAssignment (ThetaV m)) :
    (theta m).col M
      = ∑ g ∈ (pathG (2 * m)).colorings (fun v => M (some (some v))),
          (M (some none) \ {g (pathStart (2 * m)), g (pathEnd (2 * m))}).card
            * (M none \ {g (pathStart (2 * m)), g (pathEnd (2 * m))}).card :=
  col_thetaOf (2 * m) M

/-- The right-hand side of `col_theta`, spelled out so that it can be evaluated. -/
private def colThetaRHS (m : ℕ) (M : ListAssignment (ThetaV m)) : ℕ :=
  ∑ g ∈ (pathG (2 * m)).colorings (fun v => M (some (some v))),
    (M (some none) \ {g (pathStart (2 * m)), g (pathEnd (2 * m))}).card
      * (M none \ {g (pathStart (2 * m)), g (pathEnd (2 * m))}).card

#guard colThetaRHS 2 (thetaWitness 2) = 1
#guard colThetaRHS 3 (thetaWitness 3) = 1
#guard colThetaRHS 2 (constList (ThetaV 2) 2) = 2

/-! ### Level-indexed list assignments on a path -/

@[simp] lemma levelAssign_pathEnd_succ (k : ℕ) (Λ : ℕ → Finset ℕ) (h s : Finset ℕ) :
    levelAssign (k + 1) Λ h s (pathEnd (k + 1)) = h := rfl

lemma levelAssign_some (k : ℕ) (Λ : ℕ → Finset ℕ) (h s : Finset ℕ) (w : PathV k) :
    levelAssign (k + 1) Λ h s (some w) = levelAssign k Λ (Λ k) s w := rfl

/-- The list at the far end of the path is the parameter `s`. -/
@[simp] lemma levelAssign_pathStart : ∀ (k : ℕ) (Λ : ℕ → Finset ℕ) (h s : Finset ℕ),
    levelAssign k Λ h s (pathStart k) = s
  | 0, _, _, _ => rfl
  | k + 1, Λ, _, s => levelAssign_pathStart k Λ (Λ k) s

/-- Away from `pathStart`, the assignment does not depend on the parameter `s`. -/
lemma levelAssign_start_irrel : ∀ (k : ℕ) (Λ : ℕ → Finset ℕ) (h s s' : Finset ℕ) (w : PathV k),
    w ≠ pathStart k → levelAssign k Λ h s w = levelAssign k Λ h s' w
  | 0, _, _, _, _, w, hw => absurd (Subsingleton.elim w (pathStart 0)) hw
  | _ + 1, _, _, _, _, none, _ => rfl
  | k + 1, Λ, _, s, s', some w, hw =>
      levelAssign_start_irrel k Λ (Λ k) s s' w fun hc => hw (congrArg some hc)

/-- Away from `pathEnd`, the assignment does not depend on the parameter `h`. -/
lemma levelAssign_head_irrel : ∀ (k : ℕ) (Λ : ℕ → Finset ℕ) (h h' s : Finset ℕ) (w : PathV k),
    w ≠ pathEnd k → levelAssign k Λ h s w = levelAssign k Λ h' s w
  | 0, _, _, _, _, w, hw => absurd (Subsingleton.elim w (pathEnd 0)) hw
  | _ + 1, _, _, _, _, none, hw => absurd rfl hw
  | _ + 1, _, _, _, _, some _, _ => rfl

/-- Every list of a level assignment has `n` colors as soon as all the ingredients do. -/
lemma card_levelAssign (Λ : ℕ → Finset ℕ) (n : ℕ) (hΛ : ∀ j, (Λ j).card = n) :
    ∀ (k : ℕ) (h s : Finset ℕ), h.card = n → s.card = n → ∀ w : PathV k,
      (levelAssign k Λ h s w).card = n
  | 0, _, _, _, hs, _ => hs
  | _ + 1, _, _, hh, _, none => hh
  | k + 1, _, s, _, hs, some w => card_levelAssign Λ n hΛ k (Λ k) s (hΛ k) hs w

/-- A constant level assignment with matching end lists is the constant list assignment. -/
lemma levelAssign_const (P : Finset ℕ) :
    ∀ k : ℕ, levelAssign k (fun _ => P) P P = fun _ : PathV k => P
  | 0 => rfl
  | k + 1 => by
      funext w
      match w with
      | none => rfl
      | some w => exact congrFun (levelAssign_const P k) w

/-- Erasing a color at both ends of the path erases it from both end parameters. -/
lemma eraseEnds_levelAssign (k : ℕ) (Λ : ℕ → Finset ℕ) (h s : Finset ℕ) (c : ℕ) :
    eraseEnds (k + 1) c (levelAssign (k + 1) Λ h s)
      = levelAssign (k + 1) Λ (h.erase c) (s.erase c) := by
  funext w
  rw [eraseEnds]
  by_cases hw1 : w = pathStart (k + 1)
  · subst hw1
    rw [if_pos (Finset.mem_insert_self _ _), levelAssign_pathStart, levelAssign_pathStart]
  · by_cases hw2 : w = pathEnd (k + 1)
    · subst hw2
      rw [if_pos (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
        levelAssign_pathEnd_succ, levelAssign_pathEnd_succ]
    · rw [if_neg (fun hmem => by
        rcases Finset.mem_insert.mp hmem with hc | hc
        · exact hw1 hc
        · exact hw2 (Finset.mem_singleton.mp hc))]
      exact (levelAssign_start_irrel _ _ _ _ _ _ hw1).trans
        (levelAssign_head_irrel _ _ _ _ _ _ hw2)

/-- Peeling the endpoint off the path shifts the level assignment down by one. -/
theorem inducedList_levelAssign (k : ℕ) (Λ : ℕ → Finset ℕ) (h s : Finset ℕ) (c : ℕ) :
    (pathG (k + 2)).inducedList (levelAssign (k + 2) Λ h s) c
      = levelAssign (k + 1) Λ ((Λ (k + 1)).erase c) s := by
  funext w
  rw [inducedList_pathG_succ]
  by_cases hw : w = pathEnd (k + 1)
  · subst hw
    rw [if_pos rfl]
    rfl
  · rw [if_neg hw]
    exact levelAssign_head_irrel _ _ _ _ _ _ hw

/-- **The recursion.** -/
theorem col_levelAssign_step (k : ℕ) (Λ : ℕ → Finset ℕ) (h s : Finset ℕ) :
    (pathG (k + 2)).col (levelAssign (k + 2) Λ h s)
      = ∑ c ∈ h, (pathG (k + 1)).col (levelAssign (k + 1) Λ ((Λ (k + 1)).erase c) s) := by
  refine (col_pathG_succ (k + 1) (levelAssign (k + 2) Λ h s)).trans ?_
  exact Finset.sum_congr rfl fun c _ => by rw [inducedList_levelAssign]

/-- The base of the recursion: a path of length one. -/
theorem col_levelAssign_one (Λ : ℕ → Finset ℕ) (h s : Finset ℕ) :
    (pathG 1).col (levelAssign 1 Λ h s) = ∑ c ∈ h, (s.erase c).card := by
  refine (col_pathG_succ 0 (levelAssign 1 Λ h s)).trans ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [col_pathG_zero]
  congr 1

/-- An empty list at the near end of the path leaves no colorings. -/
lemma col_levelAssign_eq_zero_of_head (k : ℕ) (Λ : ℕ → Finset ℕ) (s : Finset ℕ) :
    (pathG (k + 1)).col (levelAssign (k + 1) Λ ∅ s) = 0 :=
  col_eq_zero_of_empty (pathEnd (k + 1)) (levelAssign_pathEnd_succ k Λ ∅ s)

/-- An empty list at the far end of the path leaves no colorings. -/
lemma col_levelAssign_eq_zero_of_start (k : ℕ) (Λ : ℕ → Finset ℕ) (h : Finset ℕ) :
    (pathG k).col (levelAssign k Λ h ∅) = 0 :=
  col_eq_zero_of_empty (pathStart k) (levelAssign_pathStart k Λ h ∅)

/-- **Two steps of the recursion** along a stretch where the lists are all `{p, q}`: a singleton
list `{p}` at the endpoint reappears two vertices further along. -/
theorem col_levelAssign_two_step (k : ℕ) (Λ : ℕ → Finset ℕ) (s : Finset ℕ) {p q : ℕ}
    (hne : p ≠ q) (h1 : Λ (k + 1) = {p, q}) (h2 : Λ (k + 2) = {p, q}) :
    (pathG (k + 3)).col (levelAssign (k + 3) Λ {p} s)
      = (pathG (k + 1)).col (levelAssign (k + 1) Λ {p} s) := by
  have e1 : ({p, q} : Finset ℕ).erase p = {q} := Finset.erase_insert (by simpa using hne)
  have e2 : ({p, q} : Finset ℕ).erase q = {p} := by
    rw [Finset.pair_comm]
    exact Finset.erase_insert (by simpa using hne.symm)
  rw [col_levelAssign_step, Finset.sum_singleton, h2, e1, col_levelAssign_step,
    Finset.sum_singleton, h1, e2]

/-! ### The two chains -/

lemma lvl_of_three_le {j : ℕ} (hj : 3 ≤ j) : lvl j = {1, 2} := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
  rfl

/-- **The forced chain.** For the witness lists `lvl`, prescribing the color `1` at `pathEnd` of a
path of even length `≥ 4` determines the coloring all the way along: the colors alternate
`1, 2, 1, …, 2` while the lists are `{1, 2}`, then the list `{2, 3}` forces `3` and the list
`{1, 3}` forces `1`, so the far end must avoid the color `1`. -/
theorem col_chain (s : Finset ℕ) :
    ∀ r : ℕ, (pathG (2 * r + 4)).col (levelAssign (2 * r + 4) lvl {1} s) = (s.erase 1).card
  | 0 => by
      have e31 : (lvl 3).erase 1 = ({2} : Finset ℕ) := by decide
      have e22 : (lvl 2).erase 2 = ({3} : Finset ℕ) := by decide
      have e13 : (lvl 1).erase 3 = ({1} : Finset ℕ) := by decide
      show (pathG 4).col (levelAssign 4 lvl {1} s) = _
      rw [col_levelAssign_step, Finset.sum_singleton, e31, col_levelAssign_step,
        Finset.sum_singleton, e22, col_levelAssign_step, Finset.sum_singleton, e13,
        col_levelAssign_one, Finset.sum_singleton]
  | r + 1 =>
      (col_levelAssign_two_step (2 * r + 3) lvl s (by decide)
        (lvl_of_three_le (by omega)) (lvl_of_three_le (by omega))).trans (col_chain s r)

/-- **The alternating chain.** With every interior list equal to `{x, y}` and the color `x`
prescribed at both ends of a path of even length, there is exactly one coloring. -/
theorem col_chain_const (P : Finset ℕ) (x y : ℕ) (hxy : x ≠ y) (hP : P = {x, y}) :
    ∀ r : ℕ, (pathG (2 * r + 2)).col (levelAssign (2 * r + 2) (fun _ => P) {x} {x}) = 1
  | 0 => by
      show (pathG 2).col (levelAssign 2 (fun _ => P) {x} {x}) = 1
      rw [col_levelAssign_step, Finset.sum_singleton]
      simp only [hP]
      rw [Finset.erase_insert (by simpa using hxy), col_levelAssign_one, Finset.sum_singleton,
        Finset.erase_eq_of_notMem (by simpa using Ne.symm hxy), Finset.card_singleton]
  | r + 1 =>
      (col_levelAssign_two_step (2 * r + 1) (fun _ => P) {x} hxy hP hP).trans
        (col_chain_const P x y hxy hP r)

/-! ### Peeling the two apexes of a theta graph -/

private lemma mem_some_pair {V : Type*} [DecidableEq V] (a b w : V) :
    (some w : Option V) ∈ ({some a, some b} : Finset (Option V))
      ↔ w ∈ ({a, b} : Finset V) := by
  simp

/-- **Peeling both apexes.** Summing over the colors of the two added vertices, both terminal
vertices of the long path lose both colors. -/
theorem col_thetaOf_thetaAssign (k : ℕ) (Lb La : Finset ℕ) (P : ListAssignment (PathV k)) :
    (thetaOf k).col (thetaAssign k Lb La P)
      = ∑ b ∈ Lb, ∑ a ∈ La, (pathG k).col (eraseEnds k a (eraseEnds k b P)) := by
  show (coneOn (thetaBaseOf k) {some (pathStart k), some (pathEnd k)}).col
    (optAssign Lb (optAssign La P)) = _
  rw [col_coneOn_optAssign]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hrw : (fun v => if v ∈ ({some (pathStart k), some (pathEnd k)} : Finset (Option (PathV k)))
        then ((optAssign La P) v).erase b else (optAssign La P) v)
      = optAssign La (eraseEnds k b P) := by
    funext v
    cases v with
    | none => rw [if_neg (by simp)]; rfl
    | some w =>
        show (if (some w : Option (PathV k)) ∈ _ then ((optAssign La P) (some w)).erase b
              else (optAssign La P) (some w)) = eraseEnds k b P w
        rw [eraseEnds]
        by_cases hw : w ∈ ({pathStart k, pathEnd k} : Finset (PathV k))
        · rw [if_pos ((mem_some_pair _ _ _).mpr hw), if_pos hw]
          rfl
        · rw [if_neg (fun hc => hw ((mem_some_pair _ _ _).mp hc)), if_neg hw]
          rfl
  rw [hrw]
  show (coneOn (pathG k) {pathStart k, pathEnd k}).col (optAssign La (eraseEnds k b P)) = _
  rw [col_coneOn_optAssign]
  rfl

/-! ### `col(θ_{2,2,2m}, 2) = 2` -/

/-- The theta graph is bipartite and connected, so it has exactly two colorings from the constant
list of size two. -/
theorem colConst_thetaOf (r : ℕ) : (thetaOf (2 * r + 2)).colConst 2 = 2 := by
  have hconst : (constList (Option (Option (PathV (2 * r + 2)))) 2)
      = thetaAssign (2 * r + 2) (range 2) (range 2)
          (levelAssign (2 * r + 2) (fun _ => range 2) (range 2) (range 2)) := by
    rw [levelAssign_const]
    funext v
    cases v with
    | none => rfl
    | some u => cases u <;> rfl
  rw [colConst, hconst, col_thetaOf_thetaAssign]
  simp only [eraseEnds_levelAssign, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [show ((range 2).erase 0).erase 0 = ({1} : Finset ℕ) from by decide,
    show ((range 2).erase 0).erase 1 = (∅ : Finset ℕ) from by decide,
    show ((range 2).erase 1).erase 0 = (∅ : Finset ℕ) from by decide,
    show ((range 2).erase 1).erase 1 = ({0} : Finset ℕ) from by decide,
    col_chain_const (range 2) 1 0 (by decide) (by decide) r,
    col_levelAssign_eq_zero_of_head,
    col_chain_const (range 2) 0 1 (by decide) (by decide) r]
  decide

/-! ### The witness assignment -/

lemma lvl_card : ∀ j : ℕ, (lvl j).card = 2
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- The witness is a `2`-list assignment. -/
theorem isNListAssignment_thetaWitness (m : ℕ) : IsNListAssignment (thetaWitness m) 2 := by
  intro v
  match v with
  | none => rfl
  | some none => rfl
  | some (some w) =>
      exact card_levelAssign lvl 2 lvl_card (2 * m) {1, 2} {1, 3} (by decide) (by decide) w

/-- **The witness has a single coloring.** Of the four terms of `col_thetaOf_thetaAssign`, two
vanish because a terminal vertex is left with no color at all, one vanishes because the forced
chain along the long path arrives at the far end with the only available color, and the surviving
one contributes `1`. -/
theorem col_thetaOf_witness (r : ℕ) :
    (thetaOf (2 * r + 4)).col
        (thetaAssign (2 * r + 4) {2, 3} {1, 2}
          (levelAssign (2 * r + 4) lvl {1, 2} {1, 3})) = 1 := by
  rw [col_thetaOf_thetaAssign]
  simp only [eraseEnds_levelAssign, Finset.sum_pair (by decide : (2 : ℕ) ≠ 3),
    Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
  rw [show (({1, 2} : Finset ℕ).erase 2).erase 1 = (∅ : Finset ℕ) from by decide,
    show (({1, 3} : Finset ℕ).erase 2).erase 1 = ({3} : Finset ℕ) from by decide,
    show (({1, 2} : Finset ℕ).erase 2).erase 2 = ({1} : Finset ℕ) from by decide,
    show (({1, 3} : Finset ℕ).erase 2).erase 2 = ({1, 3} : Finset ℕ) from by decide,
    show (({1, 2} : Finset ℕ).erase 3).erase 1 = ({2} : Finset ℕ) from by decide,
    show (({1, 3} : Finset ℕ).erase 3).erase 1 = (∅ : Finset ℕ) from by decide,
    show (({1, 2} : Finset ℕ).erase 3).erase 2 = ({1} : Finset ℕ) from by decide,
    show (({1, 3} : Finset ℕ).erase 3).erase 2 = ({1} : Finset ℕ) from by decide,
    col_levelAssign_eq_zero_of_head, col_chain, col_levelAssign_eq_zero_of_start, col_chain]
  decide

/-! ### `θ_{2,2,2m}` is not enumeratively chromatic-choosable at `2` -/

/-- `col(θ_{2,2,2m}, 2) = 2` for every `m ≥ 1`. -/
theorem colConst_theta (m : ℕ) (hm : 1 ≤ m) : (theta m).colConst 2 = 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  exact colConst_thetaOf r

/-- `col(θ_{2,2,2m}, L) = 1` for the witness `2`-list assignment `L`, when `m ≥ 2`. -/
theorem col_theta_witness (m : ℕ) (hm : 2 ≤ m) : (theta m).col (thetaWitness m) = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  exact col_thetaOf_witness r

/-- **`θ_{2,2,2m}` is not enumeratively chromatic-choosable at `2` for `m ≥ 2`.** -/
theorem not_ecc_theta (m : ℕ) (hm : 2 ≤ m) : ¬ (theta m).ECCAt 2 := by
  intro hmono
  have h := hmono (thetaWitness m) (isNListAssignment_thetaWitness m)
  rw [colConst_theta m (by omega), col_theta_witness m hm] at h
  omega

end ListColoring

/-! ### Theorem 2, relative to Rubin's theorem -/

namespace SimpleGraph

/-- **Kirov–Naimi, Theorem 2, relative to Rubin's theorem.**

Rubin's characterization of the `2`-choosable graphs (Erdős–Rubin–Taylor 1980) is *not* proved
anywhere in this development — it is not available in any proof assistant. It is borrowed here as
the explicit hypothesis `rubin`: for a connected graph `G`,

  `G` is `2`-choosable ⟺ the core of `G` is a single vertex, an even cycle, or `θ_{2,2,2m}`
  for some `m ≥ 1`.

The three alternatives are kept abstract (`CoreIsVertex`, `CoreIsEvenCycle`, `CoreIsTheta m`)
precisely so that the borrowed statement is visible in full and nothing about cores is smuggled in:
the only facts used about them are the four enumerative chromatic-choosability inputs, each of which
*is* proved in this development, modulo Lemma 5 (the core reduction, `ListColoring.Core`):

* `hvertex` — a graph whose core is a single vertex is a tree, hence enumeratively
  chromatic-choosable at `n` for every `n` (Kostochka–Sidorenko, `ListColoring.Cone`);
* `hcycle` — cycles are enumeratively chromatic-choosable at `n` for every `n ≥ 2` (Theorem 1,
  `ListColoring.CycleECC`);
* `hK23` — `θ_{2,2,2} = K₂,₃` is enumeratively chromatic-choosable at `2` (Lemma 6,
  `ListColoring.K23`);
* `htheta` — `θ_{2,2,2m}` is *not* enumeratively chromatic-choosable at `2` for `m ≥ 2`
  (`ListColoring.not_ecc_theta`, this file).

The conclusion is the Kirov–Naimi characterization: a connected graph is enumeratively
chromatic-choosable at `2` exactly when it is not `2`-colorable (it then has *no* coloring from
the constant list, so the inequality holds vacuously — this is the odd-cycle case) or its core is
a single vertex, an even cycle, or `K₂,₃`. -/
theorem ecc_two_iff_of_rubin {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 ↔
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.ECCAt 2)
    (hcycle : CoreIsEvenCycle → G.ECCAt 2)
    (hK23 : CoreIsTheta 1 → G.ECCAt 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.ECCAt 2) :
    G.ECCAt 2 ↔ ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 := by
  constructor
  · intro hmono
    by_cases hcol : G.Colorable 2
    · rcases rubin.mp (choosable_of_ecc_of_colorable hmono hcol) with h | h | ⟨m, hm, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · have hm1 : m = 1 := by omega
          exact Or.inr (Or.inr (Or.inr (hm1 ▸ h)))
        · exact absurd hmono (htheta m hm2 h)
    · exact Or.inl hcol
  · rintro (h | h | h | h)
    · exact ecc_of_not_colorable h
    · exact hvertex h
    · exact hcycle h
    · exact hK23 h

end SimpleGraph


