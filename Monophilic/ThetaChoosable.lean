/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Theta
import Monophilic.CycleTwo
import Monophilic.K23

/-!
# `θ_{2,2,2m}` is `2`-choosable

This file proves the substantial half of the *easy* direction of Rubin's theorem: the third family
in Rubin's list really is `2`-choosable.

> For every `m ≥ 1`, the theta graph `θ_{2,2,2m}` is `2`-choosable.

## The reduction

`Monophilic.col_theta` expresses `col(θ_{2,2,2m}, M)` as a sum over the colorings `g` of the long
path `pathG (2m)`, the summand being the product of the numbers of colors left at the two apexes,
i.e. `#(La \ {g s, g e}) * #(Lb \ {g s, g e})` where `La`, `Lb` are the two apex lists and `s`, `e`
are the two terminal vertices of the long path. So it suffices to exhibit **one** `g` whose summand
is nonzero.

For a list `L` of size two, `#(L \ {x, y}) = 0` happens exactly when `L = {x, y}`
(`Monophilic.card_sdiff_endPair_pos`), which in particular forces `x ≠ y`. Writing
`endPair k g = {g (pathStart k), g (pathEnd k)}`, the whole problem therefore becomes: find a
coloring `g` of the long path with `endPair g ≠ La` and `endPair g ≠ Lb`. Any `g` identifying the
two ends does the job, since then `endPair g` is a singleton while `La` and `Lb` have two elements.

## The path statement

The crux is thus a statement about paths of **even** length with `2`-lists
(`Monophilic.exists_ends_eq_or_three_endPairs`): either some coloring identifies the two ends, or
there are three colorings with pairwise distinct end pairs. Two lists `La`, `Lb` can block at most
two of the three, whence `Monophilic.exists_path_coloring_endPair_ne`.

The proof of the path statement splits on whether the list assignment along the path is constant.

* **Constant.** With every list equal to `{x, y}` on a path of even length, the alternating
  coloring returns to `x` at the far end. This is already available: `Monophilic.col_chain_const`
  counts the colorings with `x` prescribed at *both* ends and finds exactly one.
* **Non-constant.** Then `Monophilic.exists_reach_eq_pathStart` supplies a color `α` at `pathEnd`
  reaching *both* colors `d₁, d₂` of `L (pathStart)`. If `α` is itself one of them we get a
  coloring identifying the two ends. Otherwise `α ∉ L (pathStart)`, and `{d₁, α}`, `{d₂, α}` are
  two distinct end pairs; a coloring realizing the other color `β` at `pathEnd` gives a third one
  — again unless it identifies the two ends.

## Main results

* `Monophilic.card_sdiff_endPair_pos` : `0 < #(L \ endPair k g) ↔ L ≠ endPair k g`, for `#L = 2`
* `Monophilic.col_theta_pos_of_endPair_ne` : **the reduction** — one good path coloring suffices
* `Monophilic.col_theta_pos_of_ends_eq` : a path coloring identifying the two ends suffices
* `Monophilic.exists_ends_eq_or_three_endPairs` : **the path statement**
* `Monophilic.choosable_theta` : **`θ_{2,2,2m}` is `2`-choosable for `m ≥ 1`**
-/

open Finset

namespace Monophilic

open SimpleGraph

/-! ### Numerical checks

The two apex lists are `Lb` and `La`; along the long path the list at distance `j` from
`pathStart` is `Λ j`, except that `pathEnd` gets `h` and `pathStart` gets `s`. -/

section Guards

private def testTheta (m : ℕ) (Lb La : Finset ℕ) (Λ : ℕ → Finset ℕ) (h s : Finset ℕ) :
    ListAssignment (ThetaV m) :=
  thetaAssign (2 * m) Lb La (levelAssign (2 * m) Λ h s)

/-- The interior lists of the adversarial assignment: `{0,2}` next to `pathEnd`, `{0,1}` elsewhere.
-/
private def testLvl (m : ℕ) : ℕ → Finset ℕ := fun j => if j = 2 * m - 1 then {0, 2} else {0, 1}

-- The assignments below really are `2`-list assignments.
#guard ∀ v ∈ (univ : Finset (ThetaV 2)),
  (testTheta 2 {1, 2} {0, 3} (testLvl 2) {2, 3} {0, 1} v).card = 2
#guard ∀ v ∈ (univ : Finset (ThetaV 3)),
  (testTheta 3 {1, 2} {0, 3} (testLvl 3) {2, 3} {0, 1} v).card = 2

-- The tight configuration: along the long path every coloring gives *distinct* colors to the two
-- ends, only three unordered pairs of end colors are realized, and the two apex lists are two of
-- them. The single surviving pair still contributes.
#guard (theta 1).col (testTheta 1 {1, 2} {0, 3} (fun _ => {0, 2}) {0, 1} {2, 3}) = 2
#guard (theta 2).col (testTheta 2 {1, 2} {0, 3} (testLvl 2) {2, 3} {0, 1}) = 2
#guard (theta 3).col (testTheta 3 {1, 2} {0, 3} (testLvl 3) {2, 3} {0, 1}) = 2

-- Constant lists everywhere, and constant lists on the path with the apexes moved away.
#guard (theta 1).col (testTheta 1 {0, 1} {0, 1} (fun _ => {0, 1}) {0, 1} {0, 1}) = 2
#guard (theta 2).col (testTheta 2 {0, 1} {0, 1} (fun _ => {0, 1}) {0, 1} {0, 1}) = 2
#guard (theta 2).col (testTheta 2 {2, 3} {2, 3} (fun _ => {0, 1}) {0, 1} {0, 1}) = 8
#guard (theta 2).col (testTheta 2 {1, 2} {2, 3} (fun _ => {0, 1}) {0, 1} {0, 1}) = 6
#guard (theta 3).col (testTheta 3 {1, 2} {2, 3} (fun _ => {0, 1}) {0, 1} {0, 1}) = 6

-- The witness of `Monophilic.thetaWitness` is another `2`-list assignment, and it too is colorable.
#guard 0 < (theta 2).col (thetaWitness 2)
#guard 0 < (theta 4).col (thetaWitness 4)

/-- A small family of two-element lists to sweep over. -/
private def cands : List (Finset ℕ) := [{0, 1}, {0, 2}, {2, 3}]

-- Exhaustive check of `2`-choosability of `θ_{2,2,2}` over `cands`, and of `θ_{2,2,4}` over the
-- assignments of `cands` that are constant along the interior of the long path.
#guard ∀ Lb ∈ cands, ∀ La ∈ cands, ∀ w ∈ cands, ∀ h ∈ cands, ∀ s ∈ cands,
  0 < (theta 1).col (testTheta 1 Lb La (fun _ => w) h s)
#guard ∀ Lb ∈ cands, ∀ La ∈ cands,
  0 < (theta 2).col (testTheta 2 Lb La (fun _ => {0, 1}) {1, 2} {0, 2})

/-! `θ_{2,2,2}` is `K₂,₃`: the two branch vertices `pathStart 2` and `pathEnd 2` have degree three
and form one side, the two apexes together with the midpoint of the long path form the other. -/

private def k23L (x y u v w : Finset ℕ) : ListAssignment (Fin 2 ⊕ Fin 3) :=
  Sum.elim ![x, y] ![u, v, w]

#guard Fintype.card (ThetaV 1) = Fintype.card (Fin 2 ⊕ Fin 3)
#guard (theta 1).edgeFinset.card = (completeBipartiteGraph (Fin 2) (Fin 3)).edgeFinset.card
#guard (theta 1).colConst 2 = (completeBipartiteGraph (Fin 2) (Fin 3)).colConst 2
#guard (theta 1).colConst 3 = (completeBipartiteGraph (Fin 2) (Fin 3)).colConst 3
#guard (theta 1).colConst 4 = (completeBipartiteGraph (Fin 2) (Fin 3)).colConst 4

-- The two graphs have the same list-coloring counts on every assignment drawn from `cands`.
#guard ∀ Lb ∈ cands, ∀ La ∈ cands, ∀ w ∈ cands, ∀ h ∈ cands, ∀ s ∈ cands,
  (theta 1).col (testTheta 1 Lb La (fun _ => w) h s)
    = (completeBipartiteGraph (Fin 2) (Fin 3)).col (k23L s h Lb La w)

end Guards

/-! ### The unordered pair of colors at the two ends of a path -/

/-- The unordered pair of colors taken at the two terminal vertices of `pathG k` by a coloring
`g`. It is a singleton exactly when `g` gives the same color to both ends. -/
def endPair (k : ℕ) (g : PathV k → ℕ) : Finset ℕ := {g (pathStart k), g (pathEnd k)}

lemma endPair_eq_singleton {k : ℕ} {g : PathV k → ℕ} (h : g (pathStart k) = g (pathEnd k)) :
    endPair k g = {g (pathEnd k)} := by
  rw [endPair, h]
  exact Finset.insert_eq_self.mpr (Finset.mem_singleton_self _)

lemma card_endPair_le (k : ℕ) (g : PathV k → ℕ) : (endPair k g).card ≤ 2 :=
  (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])

/-! ### The trivial size facts about `L \ {x, y}` -/

/-- A list of size two survives the removal of a pair of colors exactly when it is not that very
pair. In particular it always survives when the two colors coincide. -/
theorem card_sdiff_endPair_pos {k : ℕ} {L : Finset ℕ} (hL : L.card = 2) (g : PathV k → ℕ) :
    0 < (L \ endPair k g).card ↔ L ≠ endPair k g := by
  rw [Finset.card_pos]
  constructor
  · rintro ⟨z, hz⟩ heq
    rw [Finset.mem_sdiff] at hz
    exact hz.2 (heq ▸ hz.1)
  · intro hne
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [Finset.sdiff_eq_empty_iff_subset] at hemp
    exact hne (Finset.eq_of_subset_of_card_le hemp (by
      rw [hL]; exact card_endPair_le k g))

/-- A list of size two keeps at least one color when the two ends of the path agree. -/
theorem endPair_ne_of_ends_eq {k : ℕ} {L : Finset ℕ} (hL : L.card = 2) {g : PathV k → ℕ}
    (h : g (pathStart k) = g (pathEnd k)) : L ≠ endPair k g := by
  intro heq
  rw [heq, endPair_eq_singleton h, Finset.card_singleton] at hL
  exact absurd hL (by omega)

/-! ### The reduction to a single path coloring

`Monophilic.col_theta` writes `col(θ_{2,2,2m}, M)` as a sum of products over the colorings of the
long path, so a single nonvanishing summand suffices. -/

/-- **The reduction.** A coloring of the long path whose pair of end colors is neither of the two
apex lists gives a coloring of the theta graph. -/
theorem col_theta_pos_of_endPair_ne (m : ℕ) (M : ListAssignment (ThetaV m))
    (hM : IsNListAssignment M 2) {g : PathV (2 * m) → ℕ}
    (hg : g ∈ (pathG (2 * m)).colorings (fun v => M (some (some v))))
    (ha : M (some none) ≠ endPair (2 * m) g) (hb : M none ≠ endPair (2 * m) g) :
    0 < (theta m).col M := by
  rw [col_theta]
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨g, hg, ?_⟩
  exact Nat.mul_pos ((card_sdiff_endPair_pos (hM (some none)) g).mpr ha)
    ((card_sdiff_endPair_pos (hM none) g).mpr hb)

/-- **The reduction, in the form that needs no case analysis.** A coloring of the long path
identifying its two terminal vertices gives a coloring of the theta graph: both apex lists have
two colors and only one is forbidden. -/
theorem col_theta_pos_of_ends_eq (m : ℕ) (M : ListAssignment (ThetaV m))
    (hM : IsNListAssignment M 2) {g : PathV (2 * m) → ℕ}
    (hg : g ∈ (pathG (2 * m)).colorings (fun v => M (some (some v))))
    (h : g (pathStart (2 * m)) = g (pathEnd (2 * m))) :
    0 < (theta m).col M :=
  col_theta_pos_of_endPair_ne m M hM hg (endPair_ne_of_ends_eq (hM (some none)) h)
    (endPair_ne_of_ends_eq (hM none) h)

/-! ### A constant `2`-list assignment on a path of even length -/

/-- Every list of a level assignment is contained in `t` as soon as all the ingredients are. -/
private lemma levelAssign_subset : ∀ (k : ℕ) (Λ : ℕ → Finset ℕ) (h s t : Finset ℕ),
    (∀ j, Λ j ⊆ t) → h ⊆ t → s ⊆ t → ∀ w : PathV k, levelAssign k Λ h s w ⊆ t
  | 0, _, _, _, _, _, _, hs, _ => hs
  | _ + 1, _, _, _, _, _, hh, _, none => hh
  | k + 1, Λ, _, s, _, hΛ, _, hs, some w => levelAssign_subset k Λ (Λ k) s _ hΛ (hΛ k) hs w

/-- **The alternating coloring.** On a path of even length, a constant `2`-list assignment admits
a coloring giving the same color to both terminal vertices: the colors alternate, and the two ends
are an even distance apart. -/
theorem exists_ends_eq_of_const (r : ℕ) {s : Finset ℕ} (hs : s.card = 2) :
    ∃ g ∈ (pathG (2 * r + 2)).colorings (fun _ => s),
      g (pathStart (2 * r + 2)) = g (pathEnd (2 * r + 2)) := by
  obtain ⟨x, y, hxy, hsxy⟩ := Finset.card_eq_two.mp hs
  have hxs : ({x} : Finset ℕ) ⊆ s := by
    rw [hsxy]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
  have hpos : 0 < (pathG (2 * r + 2)).col (levelAssign (2 * r + 2) (fun _ => s) {x} {x}) := by
    rw [col_chain_const s x y hxy hsxy r]
    exact Nat.one_pos
  rw [col_pos_iff] at hpos
  obtain ⟨g, hg⟩ := hpos
  have hsub : ∀ v, levelAssign (2 * r + 2) (fun _ => s) {x} {x} v ⊆ s :=
    levelAssign_subset (2 * r + 2) (fun _ => s) {x} {x} s (fun _ => Finset.Subset.refl s) hxs hxs
  refine ⟨g, colorings_subset_colorings hsub hg, ?_⟩
  have h1 : g (pathStart (2 * r + 2)) ∈ ({x} : Finset ℕ) := by
    have h := mem_list_of_mem_colorings hg (pathStart (2 * r + 2))
    rwa [levelAssign_pathStart] at h
  have h2 : g (pathEnd (2 * r + 2)) ∈ ({x} : Finset ℕ) :=
    mem_list_of_mem_colorings hg (pathEnd (2 * r + 2))
  rw [Finset.mem_singleton] at h1 h2
  rw [h1, h2]

/-! ### The path statement

Either some coloring identifies the two ends of the path, or three colorings have pairwise
distinct end pairs. -/

/-- Three pairwise distinct values cannot all lie in a two-element list `{A, B}`. -/
private lemma exists_ne_two {α : Type*} {t₁ t₂ t₃ A B : α}
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) :
    (t₁ ≠ A ∧ t₁ ≠ B) ∨ (t₂ ≠ A ∧ t₂ ≠ B) ∨ (t₃ ≠ A ∧ t₃ ≠ B) := by
  by_cases h1A : t₁ = A
  · by_cases h2B : t₂ = B
    · exact Or.inr (Or.inr ⟨fun h => h13 (h1A.trans h.symm), fun h => h23 (h2B.trans h.symm)⟩)
    · by_cases h2A : t₂ = A
      · exact absurd (h1A.trans h2A.symm) h12
      · exact Or.inr (Or.inl ⟨h2A, h2B⟩)
  · by_cases h1B : t₁ = B
    · by_cases h2A : t₂ = A
      · exact Or.inr (Or.inr ⟨fun h => h23 (h2A.trans h.symm), fun h => h13 (h1B.trans h.symm)⟩)
      · exact Or.inr (Or.inl ⟨h2A, fun h => h12 (h1B.trans h.symm)⟩)
    · exact Or.inl ⟨h1A, h1B⟩

/-- **The path statement.** For a `2`-list assignment on a path of even, positive length, either
some coloring gives the same color to both terminal vertices, or three colorings realize three
pairwise distinct pairs of end colors. -/
theorem exists_ends_eq_or_three_endPairs {k : ℕ} (hk : ∃ r, k = 2 * r + 2)
    (P : ListAssignment (PathV k)) (hcard : ∀ v, (P v).card = 2) :
    (∃ g ∈ (pathG k).colorings P, g (pathStart k) = g (pathEnd k)) ∨
      ∃ g₁ ∈ (pathG k).colorings P, ∃ g₂ ∈ (pathG k).colorings P, ∃ g₃ ∈ (pathG k).colorings P,
        endPair k g₁ ≠ endPair k g₂ ∧ endPair k g₁ ≠ endPair k g₃ ∧
          endPair k g₂ ≠ endPair k g₃ := by
  have hcard2 : ∀ v, 2 ≤ (P v).card := fun v => (hcard v).ge
  by_cases hconst : ∀ v, P v = P (pathEnd k)
  · -- constant lists: the alternating coloring returns to its starting color
    obtain ⟨r, rfl⟩ := hk
    have hPc : P = fun _ => P (pathEnd (2 * r + 2)) := funext hconst
    obtain ⟨g, hg, hgeq⟩ := exists_ends_eq_of_const r (hcard (pathEnd (2 * r + 2)))
    exact Or.inl ⟨g, hPc ▸ hg, hgeq⟩
  · -- non-constant lists: some color at `pathEnd` forces nothing at `pathStart`
    obtain ⟨v₀, hv₀⟩ := not_forall.mp hconst
    obtain ⟨α, hα, hreach⟩ := exists_reach_eq_pathStart hcard ⟨v₀, hv₀⟩
    by_cases hαS : α ∈ P (pathStart k)
    · -- `α` is reached from itself: that coloring identifies the two ends
      obtain ⟨f, hf, hfe, hfs⟩ := mem_reach.mp (by rw [hreach]; exact hαS)
      exact Or.inl ⟨f, hf, by rw [hfs, hfe]⟩
    · obtain ⟨d₁, d₂, hd, hS⟩ := Finset.card_eq_two.mp (hcard (pathStart k))
      have hd₁S : d₁ ∈ P (pathStart k) := by rw [hS]; exact Finset.mem_insert_self _ _
      have hd₂S : d₂ ∈ P (pathStart k) := by
        rw [hS]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      obtain ⟨f₁, hf₁, hf₁e, hf₁s⟩ := mem_reach.mp (by rw [hreach]; exact hd₁S)
      obtain ⟨f₂, hf₂, hf₂e, hf₂s⟩ := mem_reach.mp (by rw [hreach]; exact hd₂S)
      -- the other color available at `pathEnd`, and anything it reaches
      obtain ⟨β, hβ, hβα⟩ := Finset.exists_mem_ne (s := P (pathEnd k))
        (by rw [hcard (pathEnd k)]; omega) α
      obtain ⟨e, he⟩ := reach_nonempty hcard2 hβ
      obtain ⟨f₃, hf₃, hf₃e, hf₃s⟩ := mem_reach.mp he
      have heS : e ∈ P (pathStart k) := reach_subset β he
      by_cases hβe : e = β
      · exact Or.inl ⟨f₃, hf₃, by rw [hf₃s, hf₃e, hβe]⟩
      · -- the three end pairs are `{d₁, α}`, `{d₂, α}` and `{e, β}`
        have p₁ : endPair k f₁ = ({d₁, α} : Finset ℕ) := by rw [endPair, hf₁s, hf₁e]
        have p₂ : endPair k f₂ = ({d₂, α} : Finset ℕ) := by rw [endPair, hf₂s, hf₂e]
        have p₃ : endPair k f₃ = ({e, β} : Finset ℕ) := by rw [endPair, hf₃s, hf₃e]
        have hd₁α : d₁ ≠ α := fun h => hαS (h ▸ hd₁S)
        have hd₂α : d₂ ≠ α := fun h => hαS (h ▸ hd₂S)
        have heα : e ≠ α := fun h => hαS (h ▸ heS)
        refine Or.inr ⟨f₁, hf₁, f₂, hf₂, f₃, hf₃, ?_, ?_, ?_⟩
        · rw [p₁, p₂]
          intro hcon
          have : d₁ ∈ ({d₂, α} : Finset ℕ) := hcon ▸ Finset.mem_insert_self _ _
          rcases Finset.mem_insert.mp this with h | h
          · exact hd h
          · exact hd₁α (Finset.mem_singleton.mp h)
        · rw [p₁, p₃]
          intro hcon
          have hβmem : β ∈ ({d₁, α} : Finset ℕ) :=
            hcon ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          have hβd₁ : β = d₁ := by
            rcases Finset.mem_insert.mp hβmem with h | h
            · exact h
            · exact absurd (Finset.mem_singleton.mp h) hβα
          have hemem : e ∈ ({d₁, α} : Finset ℕ) := hcon ▸ Finset.mem_insert_self _ _
          rcases Finset.mem_insert.mp hemem with h | h
          · exact hβe (h.trans hβd₁.symm)
          · exact heα (Finset.mem_singleton.mp h)
        · rw [p₂, p₃]
          intro hcon
          have hβmem : β ∈ ({d₂, α} : Finset ℕ) :=
            hcon ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          have hβd₂ : β = d₂ := by
            rcases Finset.mem_insert.mp hβmem with h | h
            · exact h
            · exact absurd (Finset.mem_singleton.mp h) hβα
          have hemem : e ∈ ({d₂, α} : Finset ℕ) := hcon ▸ Finset.mem_insert_self _ _
          rcases Finset.mem_insert.mp hemem with h | h
          · exact hβe (h.trans hβd₂.symm)
          · exact heα (Finset.mem_singleton.mp h)

/-- **The path statement, in the form used for the theta graph.** Given two lists `A`, `B` of size
two, some coloring of a path of even, positive length from a `2`-list assignment has a pair of end
colors different from both. -/
theorem exists_path_coloring_endPair_ne {k : ℕ} (hk : ∃ r, k = 2 * r + 2)
    (P : ListAssignment (PathV k)) (hcard : ∀ v, (P v).card = 2) {A B : Finset ℕ}
    (hA : A.card = 2) (hB : B.card = 2) :
    ∃ g ∈ (pathG k).colorings P, A ≠ endPair k g ∧ B ≠ endPair k g := by
  rcases exists_ends_eq_or_three_endPairs hk P hcard with ⟨g, hg, hgeq⟩ | h
  · exact ⟨g, hg, endPair_ne_of_ends_eq hA hgeq, endPair_ne_of_ends_eq hB hgeq⟩
  · obtain ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, h12, h13, h23⟩ := h
    rcases exists_ne_two (A := A) (B := B) h12 h13 h23 with ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩
    · exact ⟨g₁, hg₁, Ne.symm u, Ne.symm v⟩
    · exact ⟨g₂, hg₂, Ne.symm u, Ne.symm v⟩
    · exact ⟨g₃, hg₃, Ne.symm u, Ne.symm v⟩

/-! ### `θ_{2,2,2m}` is `2`-choosable -/

/-- **`θ_{2,2,2m}` is `2`-choosable, for every `m ≥ 1`.** This is the substantial half of the easy
direction of Rubin's theorem: the third family in Rubin's list is `2`-choosable. -/
theorem choosable_theta (m : ℕ) (hm : 1 ≤ m) : (theta m).Choosable 2 := by
  intro M hM
  obtain ⟨g, hg, ha, hb⟩ :=
    exists_path_coloring_endPair_ne (k := 2 * m) ⟨m - 1, by omega⟩
      (fun v => M (some (some v))) (fun v => hM (some (some v)))
      (hM (some none)) (hM none)
  exact col_theta_pos_of_endPair_ne m M hM hg ha hb

/-- `θ_{2,2,2m}` is `2`-colorable, for every `m ≥ 1`. -/
theorem colorable_theta (m : ℕ) (hm : 1 ≤ m) : (theta m).Colorable 2 :=
  colorable_of_choosable (choosable_theta m hm)

/-- For `m ≥ 2` the graph `θ_{2,2,2m}` is `2`-choosable and yet *not* `2`-monophilic: the two
notions really are independent above the chromatic number. This is the configuration excluded by
`SimpleGraph.not_monophilic_of_colorable_of_not_choosable`, seen from the other side. -/
theorem choosable_and_not_monophilic_theta (m : ℕ) (hm : 2 ≤ m) :
    (theta m).Choosable 2 ∧ ¬ (theta m).Monophilic 2 :=
  ⟨choosable_theta m (by omega), not_monophilic_theta m hm⟩

end Monophilic

#print axioms Monophilic.card_sdiff_endPair_pos
#print axioms Monophilic.col_theta_pos_of_endPair_ne
#print axioms Monophilic.col_theta_pos_of_ends_eq
#print axioms Monophilic.exists_ends_eq_of_const
#print axioms Monophilic.exists_ends_eq_or_three_endPairs
#print axioms Monophilic.exists_path_coloring_endPair_ne
#print axioms Monophilic.choosable_theta
#print axioms Monophilic.colorable_theta
#print axioms Monophilic.choosable_and_not_monophilic_theta
