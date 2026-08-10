/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.RubinHard

/-!
# Two cycles meeting in at most one vertex are not `2`-choosable

This file proves step 3 of the classical argument for **Rubin's theorem** (A. L. Rubin, in
Erdős–Rubin–Taylor, *Choosability in graphs*, Congr. Numer. **26** (1980), 125–157): a graph
carrying two cycles that meet in at most one vertex, *joined by a path*, is not `2`-choosable.
None of the mathematics here is new; it is a step of Rubin's proof, spelled out in enough
detail for a machine.

## The connecting path is not optional

The statement usually quoted — "two cycles meeting in at most one vertex" — is stated inside a
proof about a **connected** graph, and connectivity is load-bearing. Two *disjoint* even cycles
with nothing joining them are `2`-choosable: each even cycle is (`Monophilic.choosable_two_closePath_of_odd`)
and colourings of a disjoint union are independent. Numerically, `C₄ ⊔ C₄` has four colourings
from the constant list `{1, 2}`. So the configuration formalized here is the **dumbbell**: a cycle
`A`, a cycle `B`, and a path from a vertex of `A` to a vertex of `B` meeting them only at its ends.
The path is allowed to have length `0`, which is the figure-eight — two cycles sharing exactly one
vertex. This is what a cut vertex in a connected graph of minimum degree `≥ 2` actually hands you.

## The witness

Non-`2`-choosability is certified by an explicit `2`-list assignment with **no** colouring at all,
verified by brute force before being proved (see the `#guard`s at the end of the file, and the
sweep recorded in the module docstring of `Monophilic.RubinHard` for the analogous theta witness).

Everything rests on one observation, `Monophilic.forced_chain`. Along a walk `u 0, u 1, …, u m`,
give `u (i+1)` the list `{c i, c (i+1)}` for a sequence of colours with `c i ≠ c (i+1)`. Then the
colour of `u 0` being `c 0` *forces* `u i` to be `c i` all the way along: `u (i+1)` may not repeat
the colour of `u i`, and its list has only one other element. Closing the walk into a cycle with
`c m = c 0` yields a contradiction — this is `Monophilic.no_coloring_of_cycle_chain`, and it kills
*one* prescribed colour at the base point of a cycle, **whatever the parity of the cycle**. The
parity case split that the informal argument makes is therefore not needed.

The colours are laid out by `Monophilic.armCol α β m`: `α` at index `0`, `β` at index `m`, and
`3, 4, 3, 4, …` in between. With `α, β ∈ {1, 2}` consecutive colours always differ, so every list
has exactly two elements. The full assignment is then

* the shared vertex `x` of cycle `A` and the path gets `{1, 2}`;
* cycle `A` runs `armCol 1 1 m`, so `f x = 1` is impossible;
* the path runs `armCol 2 γ l`, forcing the far end `y` to the colour `γ` once `f x = 2`;
* cycle `B` runs `armCol γ γ n`, so `f y = γ` is impossible.

Here `γ = 2` when the path is trivial (`y = x`) and `γ = 1` otherwise, which is the only place the
two shapes differ.

## Main results

* `Monophilic.forced_chain`, `Monophilic.no_coloring_of_cycle_chain` : the forcing mechanism
* `Monophilic.not_choosable_two_of_dumbbell` : **the main result** — two cycles joined by a path,
  otherwise disjoint, are not `2`-choosable
* `Monophilic.not_choosable_two_of_figureEight` : the `l = 0` case, two cycles sharing one vertex
* `Monophilic.not_choosable_two_of_odd_closed_walk` : the odd-cycle companion, restated in the
  sequence idiom this file uses. The result itself is **already proved elsewhere** — see below.

## What this file does *not* claim, because it is already done

Two of the three steps this file was written to supply turned out to exist already, and are
**not** reproved here:

* **Step 1, the core reduction.** `Monophilic.choosable_iff_of_coreIs` (`Monophilic.Theorem2`) —
  `G` is `n`-choosable iff its core is, for `n ≥ 2` — with
  `SimpleGraph.choosable_pendantTower_iff` (`Monophilic.Choosable`) underneath it. Both are
  unconditional.
* **The odd-cycle obstruction.** `Monophilic.not_colorable_two_of_hasOddCycle` and
  `Monophilic.hasOddCycle_of_not_colorable_two` (`Monophilic.Theorem2`), and
  `Monophilic.not_choosable_two_of_contains_odd_cycle` (`Monophilic.RubinHard`).
  `Monophilic.not_choosable_two_of_odd_closed_walk` below is a convenience restatement for callers
  holding a bare indexed closed walk rather than an embedded `Monophilic.closePath`; it claims
  nothing new.

`Monophilic.not_choosable_of_contains` transfers any of these obstructions to a supergraph.
-/

open Finset

namespace Monophilic

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Forced chains

The engine of the whole file. Both statements are mechanization: they are the details behind a
sentence that an informal proof would write as "the colours are then forced along the arm".
-/

/-- **Colours propagate along a chain of two-element lists.** If `u 0, u 1, …, u m` is a walk and
`u (i+1)` carries the list `{c i, c (i+1)}`, then `f (u 0) = c 0` forces `f (u i) = c i` for every
`i ≤ m`: the colour of `u (i+1)` differs from that of its predecessor `c i`, and only one other
colour is available to it.

Mechanization, not mathematics: this is the induction that an informal proof performs silently. -/
theorem forced_chain {L : ListAssignment V} {f : V → ℕ}
    (hmem : ∀ v, f v ∈ L v) (hprop : G.IsProperColoring f)
    (u : ℕ → V) (c : ℕ → ℕ) (m : ℕ)
    (hadj : ∀ i, i < m → G.Adj (u i) (u (i + 1)))
    (hL : ∀ i, i < m → L (u (i + 1)) = {c i, c (i + 1)})
    (h0 : f (u 0) = c 0) : ∀ i, i ≤ m → f (u i) = c i := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ j ih =>
      intro hj
      have hjm : j < m := hj
      have hfj : f (u j) = c j := ih (le_of_lt hjm)
      have hmemj : f (u (j + 1)) ∈ ({c j, c (j + 1)} : Finset ℕ) := by
        rw [← hL j hjm]; exact hmem _
      rcases Finset.mem_insert.mp hmemj with h | h
      · exact absurd (hfj.trans h.symm) (hprop (hadj j hjm))
      · simpa using h

/-- **A cycle of forced colours has no colouring.** With the lists of `Monophilic.forced_chain`
along a closed walk `u 0, …, u m, u 0` whose colour sequence returns to its start (`c m = c 0`),
the assumption `f (u 0) = c 0` is contradictory: the forced colour arrives back at `u m` equal to
the colour of the adjacent `u 0`.

This is the device that kills one prescribed colour at the base point of a cycle. It is insensitive
to the parity of the cycle. Mechanization of a routine step of Rubin's argument. -/
theorem no_coloring_of_cycle_chain {L : ListAssignment V} {f : V → ℕ}
    (hmem : ∀ v, f v ∈ L v) (hprop : G.IsProperColoring f)
    (u : ℕ → V) (c : ℕ → ℕ) (m : ℕ)
    (hadj : ∀ i, i < m → G.Adj (u i) (u (i + 1))) (hcl : G.Adj (u m) (u 0))
    (hL : ∀ i, i < m → L (u (i + 1)) = {c i, c (i + 1)})
    (hc : c m = c 0) (h0 : f (u 0) = c 0) : False :=
  hprop hcl ((forced_chain hmem hprop u c m hadj hL h0 m le_rfl).trans (hc.trans h0.symm))

/-! ### The colour pattern along an arm -/

/-- The colours along an arm of `m` steps: `α` at the near end, `β` at the far end, and the two
auxiliary colours `3, 4` alternating in between. For `α, β ∈ {1, 2}` consecutive values always
differ, which is exactly what `Monophilic.forced_chain` needs.

A definition of this development, introduced to give the witness assignment a closed form. -/
def armCol (a b m : ℕ) : ℕ → ℕ := fun i =>
  if i = 0 then a else if m ≤ i then b else if i % 2 = 1 then 3 else 4

@[simp] lemma armCol_zero (a b m : ℕ) : armCol a b m 0 = a := by simp [armCol]

/-- The far end of an arm carries the colour `β`, including in the degenerate case `m = 0` where
the two ends coincide and `α = β` is required. -/
lemma armCol_end (a b m : ℕ) (h : m = 0 → a = b) : armCol a b m m = b := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using h rfl
  · have hm0 : m ≠ 0 := by omega
    simp [armCol, hm0]

/-- **Consecutive colours along an arm differ**, so every list `{c i, c (i+1)}` really has two
elements. The hypothesis `m = 1 → a ≠ b` covers the one-step arm, where the two ends are adjacent
and no auxiliary colour intervenes. Mechanization. -/
lemma armCol_ne {a b : ℕ} (ha : a = 1 ∨ a = 2) (hb : b = 1 ∨ b = 2) {m i : ℕ}
    (hab : m = 1 → a ≠ b) (hi : i < m) :
    armCol a b m i ≠ armCol a b m (i + 1) := by
  by_cases hm1 : m = 1
  · subst hm1
    have hi0 : i = 0 := by omega
    subst hi0
    simpa [armCol] using hab rfl
  · have hm2 : 2 ≤ m := by omega
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [armCol] <;> split_ifs <;> first | contradiction | omega

/-- The lists along an arm: the base point gets `{1, 2}`, and the `i+1`-st vertex gets
`{c i, c (i+1)}`, which is what `Monophilic.forced_chain` consumes. -/
def armLists (c : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => {1, 2}
  | i + 1 => {c i, c (i + 1)}

lemma armLists_card {c : ℕ → ℕ} {m : ℕ} (h : ∀ i, i < m → c i ≠ c (i + 1)) :
    ∀ i, i ≤ m → (armLists c i).card = 2 := by
  intro i hi
  match i with
  | 0 => show (({1, 2} : Finset ℕ)).card = 2; decide
  | j + 1 => exact Finset.card_pair (h j hi)

/-! ### Prescribing a list assignment along an indexed family

Pure bookkeeping: a graph's vertices are an unstructured type, and the witness is described by
walking along three sequences of them. `Monophilic.ofSeq` transports lists from indices to
vertices, and the three sequences are layered so that the earlier ones win at the two shared
vertices. -/

open Classical in
/-- Prescribe the lists `M i` at the vertices `u i` for `i ≤ m`, falling back to `dflt` elsewhere.
Well defined at `u j` as soon as `u` is injective on `{0, …, m}`. Mechanization. -/
noncomputable def ofSeq (u : ℕ → V) (m : ℕ) (M : ℕ → Finset ℕ) (dflt : V → Finset ℕ) :
    V → Finset ℕ :=
  fun w => if h : ∃ i, i ≤ m ∧ u i = w then M h.choose else dflt w

lemma ofSeq_apply {u : ℕ → V} {m : ℕ} (M : ℕ → Finset ℕ) (dflt : V → Finset ℕ)
    (hinj : Set.InjOn u (Set.Iic m)) {j : ℕ} (hj : j ≤ m) :
    ofSeq u m M dflt (u j) = M j := by
  classical
  have h : ∃ i, i ≤ m ∧ u i = u j := ⟨j, hj, rfl⟩
  have hs := h.choose_spec
  have : h.choose = j := hinj hs.1 hj hs.2
  simp only [ofSeq, dif_pos h, this]

lemma ofSeq_of_notMem {u : ℕ → V} {m : ℕ} (M : ℕ → Finset ℕ) (dflt : V → Finset ℕ) {w : V}
    (hw : ∀ i, i ≤ m → u i ≠ w) : ofSeq u m M dflt w = dflt w := by
  classical
  have h : ¬ ∃ i, i ≤ m ∧ u i = w := fun ⟨i, hi, he⟩ => hw i hi he
  simp only [ofSeq, dif_neg h]

lemma ofSeq_card {u : ℕ → V} {m : ℕ} {M : ℕ → Finset ℕ} {dflt : V → Finset ℕ}
    (hM : ∀ i, i ≤ m → (M i).card = 2) (hd : ∀ w, (dflt w).card = 2) (w : V) :
    (ofSeq u m M dflt w).card = 2 := by
  classical
  by_cases h : ∃ i, i ≤ m ∧ u i = w
  · rw [ofSeq, dif_pos h]; exact hM _ h.choose_spec.1
  · rw [ofSeq, dif_neg h]; exact hd w

/-! ### A closed walk of odd length

The companion to the main theorem. An odd closed walk is not even `2`-colourable, so the constant
list `{0, 1}` already has no colouring. This is the classical odd-cycle obstruction; no injectivity
is required, because the constant list assignment does not depend on the indexing. -/

/-- **A graph with a closed walk of odd length is not `2`-choosable.** `u 0, u 1, …, u m, u 0`
with `m` even has odd length `m + 1`, and the constant list assignment `{0, 1}` leaves it
with no colouring — the two colours must alternate and come back in phase.

Classical, and **not a new result even within this development**: it is the odd-cycle half of
"`2`-colourable iff bipartite", already available as
`Monophilic.not_colorable_two_of_hasOddCycle` (`Monophilic.Theorem2`) and as
`Monophilic.not_choosable_two_of_contains_odd_cycle` (`Monophilic.RubinHard`). Both of those want
an embedded copy of `Monophilic.closePath`, which costs an injectivity obligation; this restatement
takes a bare indexed closed walk, matching the interface of
`Monophilic.not_choosable_two_of_dumbbell` below, and is proved directly from
`Monophilic.no_coloring_of_cycle_chain` in five lines. Convenience, not mathematics. -/
theorem not_choosable_two_of_odd_closed_walk {m : ℕ} (hm : Even m) (u : ℕ → V)
    (hadj : ∀ i, i < m → G.Adj (u i) (u (i + 1))) (hcl : G.Adj (u m) (u 0)) :
    ¬ G.Choosable 2 := by
  intro hch
  obtain ⟨f, hf⟩ := col_pos_iff.mp (hch (constList V 2) (isNListAssignment_constList 2))
  rw [mem_colorings] at hf
  obtain ⟨hmem, hprop⟩ := hf
  have h2 : f (u 0) < 2 := by
    have := hmem (u 0); simpa [constList_apply] using this
  -- the two colours, in the order in which the walk meets them
  obtain ⟨p, q, hp2, hq2, hpq, hp⟩ :
      ∃ p q : ℕ, p < 2 ∧ q < 2 ∧ p ≠ q ∧ f (u 0) = p :=
    ⟨f (u 0), 1 - f (u 0), h2, by omega, by omega, rfl⟩
  have hpair : ({p, q} : Finset ℕ) = Finset.range 2 := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · simp only [Finset.mem_range]
      rcases Finset.mem_insert.mp hx with h | h
      · omega
      · simp only [Finset.mem_singleton] at h; omega
    · rw [Finset.card_range, Finset.card_pair hpq]
  refine no_coloring_of_cycle_chain hmem hprop u (fun i => if i % 2 = 0 then p else q) m
    hadj hcl (fun i _ => ?_) ?_ (by simpa using hp)
  · simp only [constList_apply]
    rcases Nat.even_or_odd i with h | h
    · have h1 : i % 2 = 0 := Nat.even_iff.mp h
      have h2 : (i + 1) % 2 ≠ 0 := by omega
      simp only [if_pos h1, if_neg h2, hpair]
    · have h1 : i % 2 ≠ 0 := by have := Nat.odd_iff.mp h; omega
      have h2 : (i + 1) % 2 = 0 := by have := Nat.odd_iff.mp h; omega
      rw [if_neg h1, if_pos h2, Finset.pair_comm q p]
      exact hpair.symm
  · have : m % 2 = 0 := Nat.even_iff.mp hm
    simp [this]

/-! ### The dumbbell

The main theorem. The configuration is: a cycle `A 0, …, A m, A 0`; a path `P 0, …, P l` starting
at `A 0` and ending at `B 0`; and a cycle `B 0, …, B n, B 0`. The three are disjoint apart from
those two identifications, and `l = 0` is allowed — then `P 0 = P l`, the two cycles share the
single vertex `A 0 = B 0`, and the configuration is a figure-eight. -/

/-- **Two cycles joined by a path, otherwise disjoint, are not `2`-choosable.**

The data is a cycle `A 0, …, A m, A 0` on `m + 1 ≥ 3` vertices, a cycle `B 0, …, B n, B 0` on
`n + 1 ≥ 3` vertices, and a path `P 0, …, P l` from `P 0 = A 0` to `P l = B 0` whose interior
avoids both cycles. Taking `l = 0` identifies `A 0` with `B 0` and gives two cycles meeting in
exactly one vertex.

This is **step 3 of Rubin's proof** of the classification of `2`-choosable graphs (A. L. Rubin, in
Erdős–Rubin–Taylor, *Choosability in graphs*, Congr. Numer. **26** (1980), 125–157). It is not a
new result. The witness assignment and its verification are this development's, but the argument —
force one colour at the branch vertex round the first cycle, propagate along the path, and force
the other round the second — is Rubin's.

Note the path is genuinely needed and is not an artifact of the formalization: two *disjoint* even
cycles with nothing joining them are `2`-choosable. In Rubin's setting the graph is connected, so
the path is always available. -/
theorem not_choosable_two_of_dumbbell {m n l : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (A P B : ℕ → V)
    (hA : ∀ i, i < m → G.Adj (A i) (A (i + 1))) (hAcl : G.Adj (A m) (A 0))
    (hP : ∀ j, j < l → G.Adj (P j) (P (j + 1)))
    (hB : ∀ k, k < n → G.Adj (B k) (B (k + 1))) (hBcl : G.Adj (B n) (B 0))
    (hPA : P 0 = A 0) (hPB : P l = B 0)
    (hAinj : Set.InjOn A (Set.Iic m)) (hPinj : Set.InjOn P (Set.Iic l))
    (hBinj : Set.InjOn B (Set.Iic n))
    (hAP : ∀ i, i ≤ m → ∀ j, 1 ≤ j → j ≤ l → A i ≠ P j)
    (hAB : ∀ i, i ≤ m → ∀ k, 1 ≤ k → k ≤ n → A i ≠ B k)
    (hPB' : ∀ j, j ≤ l → ∀ k, 1 ≤ k → k ≤ n → P j ≠ B k) :
    ¬ G.Choosable 2 := by
  classical
  -- the colour that the path delivers at its far end
  set g : ℕ := if l = 0 then 2 else 1 with hg
  have hg12 : g = 1 ∨ g = 2 := by
    rcases Nat.eq_zero_or_pos l with h | h
    · simp [hg, h]
    · have : l ≠ 0 := by omega
      simp [hg, this]
  set cA : ℕ → ℕ := armCol 1 1 m with hcA
  set cP : ℕ → ℕ := armCol 2 g l with hcP
  set cB : ℕ → ℕ := armCol g g n with hcB
  -- consecutive colours differ along each of the three arms
  have hneA : ∀ i, i < m → cA i ≠ cA (i + 1) := fun i hi =>
    armCol_ne (Or.inl rfl) (Or.inl rfl) (fun h => absurd h (by omega)) hi
  have hneP : ∀ j, j < l → cP j ≠ cP (j + 1) := fun j hj =>
    armCol_ne (Or.inr rfl) hg12 (fun h => by simp [hg, h]) hj
  have hneB : ∀ k, k < n → cB k ≠ cB (k + 1) := fun k hk =>
    armCol_ne hg12 hg12 (fun h => absurd h (by omega)) hk
  -- the witness
  set base : V → Finset ℕ := fun _ => ({0, 1} : Finset ℕ) with hbase
  set LB : V → Finset ℕ := ofSeq B n (armLists cB) base with hLB
  set LP : V → Finset ℕ := ofSeq P l (armLists cP) LB with hLP
  set L : V → Finset ℕ := ofSeq A m (armLists cA) LP with hL
  -- every list has two colours
  have hcard : IsNListAssignment L 2 := by
    have hbc : ∀ w : V, (base w).card = 2 := fun _ => by decide
    have h1 : ∀ w, (LB w).card = 2 := fun w =>
      ofSeq_card (armLists_card hneB) hbc w
    have h2 : ∀ w, (LP w).card = 2 := fun w =>
      ofSeq_card (armLists_card hneP) h1 w
    exact fun w => ofSeq_card (armLists_card hneA) h2 w
  intro hch
  obtain ⟨f, hf⟩ := col_pos_iff.mp (hch L hcard)
  rw [mem_colorings] at hf
  obtain ⟨hmem, hprop⟩ := hf
  -- read off the lists on each of the three arms
  have hLA : ∀ i, i ≤ m → L (A i) = armLists cA i := fun i hi =>
    ofSeq_apply _ _ hAinj hi
  have hLPa : ∀ j, 1 ≤ j → j ≤ l → L (P j) = armLists cP j := by
    intro j hj1 hj2
    have h1 : L (P j) = LP (P j) :=
      ofSeq_of_notMem _ _ (fun i hi => hAP i hi j hj1 hj2)
    rw [h1, hLP, ofSeq_apply _ _ hPinj hj2]
  have hLBa : ∀ k, 1 ≤ k → k ≤ n → L (B k) = armLists cB k := by
    intro k hk1 hk2
    have h1 : L (B k) = LP (B k) :=
      ofSeq_of_notMem _ _ (fun i hi => hAB i hi k hk1 hk2)
    have h2 : LP (B k) = LB (B k) :=
      ofSeq_of_notMem _ _ (fun j hj => hPB' j hj k hk1 hk2)
    rw [h1, h2, hLB, ofSeq_apply _ _ hBinj hk2]
  -- the branch vertex has the list `{1, 2}`
  have hx : f (A 0) = 1 ∨ f (A 0) = 2 := by
    have := hmem (A 0)
    rw [hLA 0 (by omega)] at this
    simpa [armLists] using this
  rcases hx with hx | hx
  · -- the first cycle rules out the colour `1`
    refine no_coloring_of_cycle_chain hmem hprop A cA m hA hAcl ?_ ?_ (by rw [hx, hcA]; simp)
    · intro i hi; rw [hLA (i + 1) hi]; rfl
    · rw [hcA, armCol_end 1 1 m (fun _ => rfl), armCol_zero]
  · -- the path delivers the colour `g` at `B 0`, and the second cycle rules it out
    have hPl : f (P l) = g := by
      have h0 : f (P 0) = cP 0 := by rw [hPA, hx, hcP, armCol_zero]
      have := forced_chain hmem hprop P cP l hP (fun j hj => by
        rw [hLPa (j + 1) (by omega) hj]; rfl) h0 l le_rfl
      rw [this, hcP, armCol_end 2 g l (fun h => by simp [hg, h])]
    refine no_coloring_of_cycle_chain hmem hprop B cB n hB hBcl ?_ ?_ ?_
    · intro k hk; rw [hLBa (k + 1) (by omega) hk]; rfl
    · rw [hcB, armCol_end g g n (fun _ => rfl), armCol_zero]
    · rw [← hPB, hPl, hcB, armCol_zero]

/-- **Two cycles sharing exactly one vertex are not `2`-choosable.** The `l = 0` case of
`Monophilic.not_choosable_two_of_dumbbell`: cycles `A 0, …, A m, A 0` and `B 0, …, B n, B 0` with
`A 0 = B 0` their only common vertex.

Step 3 of Rubin's proof (Erdős–Rubin–Taylor 1980); not a new result. -/
theorem not_choosable_two_of_figureEight {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (A B : ℕ → V)
    (hA : ∀ i, i < m → G.Adj (A i) (A (i + 1))) (hAcl : G.Adj (A m) (A 0))
    (hB : ∀ k, k < n → G.Adj (B k) (B (k + 1))) (hBcl : G.Adj (B n) (B 0))
    (hAB0 : A 0 = B 0)
    (hAinj : Set.InjOn A (Set.Iic m)) (hBinj : Set.InjOn B (Set.Iic n))
    (hdisj : ∀ i, i ≤ m → ∀ k, 1 ≤ k → k ≤ n → A i ≠ B k) :
    ¬ G.Choosable 2 :=
  not_choosable_two_of_dumbbell (l := 0) hm hn A (fun _ => A 0) B hA hAcl
    (fun _ h => absurd h (by omega)) hB hBcl rfl hAB0 hAinj
    (fun _ hx _ hy _ => by
      simp only [Set.mem_Iic] at hx hy; omega)
    hBinj
    (fun _ _ _ hj1 hj0 => absurd hj0 (by omega))
    hdisj
    (fun j hj k hk1 hk2 => by
      have : j = 0 := by omega
      subst this; exact hdisj 0 (by omega) k hk1 hk2)

/-! ### Numerical verification

The witness of `Monophilic.not_choosable_two_of_dumbbell` was checked by brute force before it was
proved. The checks below rebuild the dumbbell on `Fin N` from an explicit edge list, give it the
very same lists, and count the colourings: there are none, for every shape in the sweep. The
degree sequences confirm the graphs really are dumbbells — two vertices of degree three, or one of
degree four when the cycles meet.

The last three checks are the reason the connecting path appears in the statement at all: two
*disjoint* `4`-cycles have four colourings from the constant list `{1, 2}` and so are not covered
by any such witness. -/

section Guards

/-- A graph on `Fin N` from an explicit list of index pairs. -/
private def mkG (N : ℕ) (es : List (ℕ × ℕ)) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (fun i j => (i.val, j.val) ∈ es)

private instance (N : ℕ) (es : List (ℕ × ℕ)) : DecidableRel (mkG N es).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ _))

/-- Edges of the dumbbell with cycles of `m + 1` and `n + 1` vertices joined by `l` edges. -/
private def dumbEdges (m n l : ℕ) : List (ℕ × ℕ) :=
  let P : ℕ → ℕ := fun j => if j = 0 then 0 else m + j
  let B : ℕ → ℕ := fun k => if k = 0 then P l else m + l + k
  ((List.range m).map fun i => (i, i + 1)) ++ [(m, 0)] ++
  ((List.range l).map fun j => (P j, P (j + 1))) ++
  ((List.range n).map fun k => (B k, B (k + 1))) ++ [(B n, B 0)]

/-- The witness lists, read off the index of the vertex exactly as in the proof. -/
private def dumbL (m n l : ℕ) : ℕ → Finset ℕ := fun v =>
  let g : ℕ := if l = 0 then 2 else 1
  if v = 0 then {1, 2}
  else if v ≤ m then {armCol 1 1 m (v - 1), armCol 1 1 m v}
  else if v ≤ m + l then ({armCol 2 g l (v - m - 1), armCol 2 g l (v - m)} : Finset ℕ)
  else {armCol g g n (v - m - l - 1), armCol g g n (v - m - l)}

private abbrev dumbG (m n l : ℕ) : SimpleGraph (Fin (m + l + n + 1)) := mkG _ (dumbEdges m n l)

private def dumbCol (m n l : ℕ) : ℕ := (dumbG m n l).col (fun v => dumbL m n l v.val)

private def dumbDegs (m n l : ℕ) : List ℕ :=
  (List.finRange (m + l + n + 1)).map fun v => (dumbG m n l).degree v

-- the shapes are what we think they are
#guard dumbDegs 2 2 0 = [4, 2, 2, 2, 2]              -- two triangles sharing a vertex
#guard dumbDegs 3 3 0 = [4, 2, 2, 2, 2, 2, 2]        -- two `4`-cycles sharing a vertex
#guard dumbDegs 3 3 1 = [3, 2, 2, 2, 3, 2, 2, 2]     -- joined by an edge
#guard dumbDegs 3 3 2 = [3, 2, 2, 2, 2, 3, 2, 2, 2]  -- joined by a path of length two

-- every list really has two colours
#guard ((List.range 6).flatMap fun m => (List.range 6).flatMap fun n =>
  (List.range 6).map fun l =>
    ((List.range (m + 2 + l + n + 2 + 1)).map fun v =>
      (dumbL (m + 2) (n + 2) l v).card)).all fun cs => cs.all (· == 2)

-- and there is no colouring at all, for every shape in the sweep
#guard ((List.range 5).flatMap fun m => (List.range 5).flatMap fun n =>
  (List.range 5).map fun l => dumbCol (m + 2) (n + 2) l).all (· == 0)

-- sanity, and the reason the connecting path is part of the statement
#guard (mkG 4 [(0, 1), (1, 2), (2, 3), (3, 0)]).col (fun _ => ({1, 2} : Finset ℕ)) = 2
#guard (mkG 3 [(0, 1), (1, 2), (2, 0)]).col (fun _ => ({1, 2} : Finset ℕ)) = 0
#guard (mkG 8 [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4)]).col
  (fun _ => ({1, 2} : Finset ℕ)) = 4

end Guards

#print axioms Monophilic.forced_chain
#print axioms Monophilic.no_coloring_of_cycle_chain
#print axioms Monophilic.not_choosable_two_of_odd_closed_walk
#print axioms Monophilic.not_choosable_two_of_dumbbell
#print axioms Monophilic.not_choosable_two_of_figureEight

end Monophilic
