/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Fin
import Cacti.RootedProfile
import Cacti.BalancedCore
import Cacti.Tensor
import Cacti.EvenTensor
import Cacti.RefTensor
import Cacti.PathCone
import Cacti.EvenBridge
import Cacti.Induction

/-!
# The `k = 3` route: the bridge inequality

At `k = 3` the pair bound of `Cacti/Induction.lean` is false, and the induction has to carry GM
dominance instead: weights `w` are dominated by a normalizer `W` when
`(W v) ^ 3 ≤ ∏_{c ∈ L v} w v c`,
and the invariant becomes `(A · ∏ᵥ W v) ^ 3 ≤ ∏_{c ∈ L r} rootedWcol G L w r c` (handoff §5.6).

This file holds the elementary inequality that route needs where the `k ≥ 4` one used
`bridge_sum_ge`: across a pendant edge the three complementary sums have product at least `8`
times the product of the weights, `8` being the cube of the uniform pendant factor `k - 1 = 2`.
-/

namespace ListColoring

open Finset

/-- **GM dominance survives pendant absorption** at `k = 3`: the absorbed weight
`c ↦ ∑_{e ∈ Lx, e ≠ c} wx e` at the neighbour of a pendant vertex is dominated by `2 · Wx`, the
pendant factor times the pendant's own normalizer. The three complementary sums are matched to
the three list colours by an equality-extending bijection, so `gm_bridge_prod` applies. -/
theorem pendant_gm_dominant {Lx Lu : Finset ℕ} (hLx : Lx.card = 3) (hLu : Lu.card = 3)
    (wx : ℕ → ℕ) {Wx : ℕ} (hdx : Wx ^ 3 ≤ ∏ e ∈ Lx, wx e) :
    8 * Wx ^ 3 ≤ ∏ c ∈ Lu, ∑ e ∈ Lx.filter (· ≠ c), wx e := by
  classical
  obtain ⟨τ, hτmem, hτinj⟩ := exists_enum hLu
  obtain ⟨σ, hσmem, hσinj, hmatch⟩ := exists_extendEnum hLu hLx τ hτmem hτinj
  -- each complementary sum dominates the one that erases the matched colour
  have hstep : ∀ i : Fin 3, (∑ e ∈ Lx.erase (σ i), wx e) ≤ ∑ e ∈ Lx.filter (· ≠ τ i), wx e := by
    intro i
    refine Finset.sum_le_sum_of_subset (fun e he => ?_)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_of_mem_erase he, fun hcon => ?_⟩
    by_cases hiL : τ i ∈ Lx
    · exact Finset.ne_of_mem_erase he (hcon.trans (hmatch i hiL).symm)
    · exact hiL (hcon ▸ Finset.mem_of_mem_erase he)
  calc 8 * Wx ^ 3 ≤ 8 * ∏ e ∈ Lx, wx e := Nat.mul_le_mul_left _ hdx
    _ ≤ ∏ e ∈ Lx, ∑ d ∈ Lx.erase e, wx d := gm_bridge_prod hLx wx
    _ = ∏ i : Fin 3, ∑ d ∈ Lx.erase (σ i), wx d := by
        rw [← enum_image hLx hσmem hσinj, Finset.prod_image (fun i _ j _ h => hσinj h)]
    _ ≤ ∏ i : Fin 3, ∑ e ∈ Lx.filter (· ≠ τ i), wx e :=
        Finset.prod_le_prod' (fun i _ => hstep i)
    _ = ∏ c ∈ Lu, ∑ e ∈ Lx.filter (· ≠ c), wx e := by
        rw [← enum_image hLu hτmem hτinj, Finset.prod_image (fun i _ j _ h => hτinj h)]

section Cut

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The cut-vertex step for GM dominance**: with `V` split at `u` into `A` and `B` and the root
in `A`, the GM bound on both sides gives it for `G`. The `B` side is absorbed into the weight at
`u`, where its uniform count times its normalizer product becomes the new normalizer — the same
decomposition `pair_bound_of_cut` performs, with the pair of coordinates replaced by the product
over the root's list. -/
theorem gm_bound_of_cut {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {u : V} (huA : u ∈ A) (huB : u ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = u)
    (hedge : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {r : V} (hrA : r ∈ A) {k : ℕ} (hk : 1 ≤ k)
    (L : ListAssignment V) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ k ≤ ∏ c ∈ L v, w v c)
    (hBside : ∀ (wB : B → ℕ → ℕ) (WB : B → ℕ),
      (∀ x, (WB x) ^ k ≤ ∏ c ∈ L x.val, wB x c) →
        (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 * ∏ x, WB x) ^ k ≤
          ∏ c ∈ L u, rootedWcol (G.induce B) (fun x => L x.val) wB ⟨u, huB⟩ c)
    (hAside : ∀ (wA : A → ℕ → ℕ) (WA : A → ℕ),
      (∀ v, (WA v) ^ k ≤ ∏ c ∈ L v.val, wA v c) →
        (rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ 0 * ∏ v, WA v) ^ k ≤
          ∏ c ∈ L r, rootedWcol (G.induce A) (fun v => L v.val) wA ⟨r, hrA⟩ c) :
    (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ k ≤
      ∏ c ∈ L r, rootedWcol G L w r c := by
  -- the `B` side, with `u`'s own weight charged to the `A` side
  have hB := hBside (fun x e => if x.val = u then 1 else w x.val e)
    (fun x => if x.val = u then 1 else W x.val) (by
      intro x
      by_cases hxu : x.val = u
      · simp only [if_pos hxu, one_pow, Finset.prod_const_one, le_refl]
      · simp only [if_neg hxu]
        exact hdom x.val)
  -- the absorbed weight at `u` is still GM-dominant, over the `B`-side normalizer
  have hA := hAside
    (fun v d' => if v.val = u then
        w u d' * rootedWcol (G.induce B) (fun x => L x.val)
          (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ d'
      else w v.val d')
    (fun v => if v.val = u then
        W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
          ∏ x : B, (if x.val = u then 1 else W x.val))
      else W v.val)
    (by
      intro v
      by_cases hvu : v.val = u
      · simp only [hvu]
        calc (W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
                ∏ x : B, (if x.val = u then 1 else W x.val))) ^ k
            = W u ^ k * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
                ∏ x : B, (if x.val = u then 1 else W x.val)) ^ k := by rw [mul_pow]
          _ ≤ (∏ c ∈ L u, w u c) *
              ∏ c ∈ L u, rootedWcol (G.induce B) (fun x => L x.val)
                  (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ c :=
              Nat.mul_le_mul (hdom u) hB
          _ = _ := (Finset.prod_mul_distrib).symm
      · simp only [if_neg hvu]
        exact hdom v.val)
  -- rewrite the goal through absorption, then match the normalizer products
  rw [Finset.prod_congr rfl (fun c _ =>
      rootedWcol_absorb huA huB hcover hmeet hedge hrA L w c),
    rootedCol_absorb_uniform huA huB hcover hmeet hedge hrA hk 0]
  have hWA : (∏ v : A, (if v.val = u then
        W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
          ∏ x : B, (if x.val = u then 1 else W x.val))
      else W v.val))
      = (W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
          ∏ x : B, (if x.val = u then 1 else W x.val))) *
        ∏ v ∈ Finset.univ.erase (⟨u, huA⟩ : A), W v.val := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨u, huA⟩ : A)), if_pos rfl]
    congr 1
    exact Finset.prod_congr rfl fun v hv =>
      if_neg (fun h => Finset.ne_of_mem_erase hv (Subtype.ext h))
  have hWAu : W u * ∏ v ∈ Finset.univ.erase (⟨u, huA⟩ : A), W v.val = ∏ v : A, W v.val :=
    Finset.mul_prod_erase Finset.univ (fun v : A => W v.val)
      (Finset.mem_univ (⟨u, huA⟩ : A))
  have hAB : (∏ v, W v) = (∏ v : A, W v.val) * ∏ x : B, (if x.val = u then 1 else W x.val) := by
    have hA' : (∏ v : A, W v.val) = ∏ v ∈ A.toFinset, W v :=
      (Finset.prod_subtype A.toFinset (fun _ => Set.mem_toFinset) W).symm
    have hB' : (∏ x : B, (if x.val = u then 1 else W x.val))
        = ∏ x ∈ B.toFinset, (if x = u then 1 else W x) :=
      (Finset.prod_subtype B.toFinset (fun _ => Set.mem_toFinset)
        (fun x => if x = u then 1 else W x)).symm
    have huBF : u ∈ B.toFinset := Set.mem_toFinset.mpr huB
    have hBerase : (∏ x ∈ B.toFinset, (if x = u then 1 else W x))
        = ∏ x ∈ B.toFinset.erase u, W x := by
      rw [← Finset.mul_prod_erase B.toFinset (fun x => if x = u then 1 else W x) huBF,
        if_pos rfl, one_mul]
      exact Finset.prod_congr rfl fun x hx => if_neg (Finset.ne_of_mem_erase hx)
    have hdisj : Disjoint A.toFinset (B.toFinset.erase u) := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      exact Finset.ne_of_mem_erase hxB
        (hmeet x (Set.mem_toFinset.mp hxA)
          (Set.mem_toFinset.mp (Finset.mem_of_mem_erase hxB)))
    have huniv : (Finset.univ : Finset V) = A.toFinset ∪ B.toFinset.erase u := by
      refine (Finset.eq_univ_of_forall fun v => ?_).symm
      rcases hcover v with h | h
      · exact Finset.mem_union_left _ (Set.mem_toFinset.mpr h)
      · by_cases hvu : v = u
        · exact Finset.mem_union_left _ (Set.mem_toFinset.mpr (hvu ▸ huA))
        · exact Finset.mem_union_right _
            (Finset.mem_erase.mpr ⟨hvu, Set.mem_toFinset.mpr h⟩)
    rw [hA', hB', hBerase, ← Finset.prod_union hdisj]
    exact Finset.prod_congr huniv fun _ _ => rfl
  have hprod : rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
        rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ 0 * ∏ v, W v
      = rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ 0 *
        ∏ v : A, (if v.val = u then
            W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
              ∏ x : B, (if x.val = u then 1 else W x.val))
          else W v.val) := by
    rw [hWA, hAB, ← hWAu]
    ring
  rw [hprod]
  exact hA

end Cut

section Balanced

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The uniform normalizer of a cycle does not depend on the vertex**: rotating the indexing
keeps the cyclic adjacency, so every vertex sees the same uniform rooted count `A`. The balanced
core has to hit this same `A` at every vertex, which is why it is worth recording. -/
theorem rootedCol_constList_cycle_vertex {m k : ℕ} (hk : 1 ≤ k) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)) (i : Fin (m + 1)) :
    rootedCol G (constList V k) (ix i) 0 = rootedCol G (constList V k) (ix 0) 0 := by
  have hrot : ∀ a b : Fin (m + 1),
      G.Adj (((Equiv.addRight i).trans ix) a) (((Equiv.addRight i).trans ix) b) ↔
        (b = a + 1 ∨ a = b + 1) := by
    intro a b
    show G.Adj (ix (a + i)) (ix (b + i)) ↔ _
    rw [hadj]
    have hcancel : ∀ p q : Fin (m + 1), (p + i = q + i + 1) ↔ p = q + 1 := by
      intro p q
      rw [add_right_comm q i 1, add_left_inj]
    rw [hcancel, hcancel]
  have h0 : ((Equiv.addRight i).trans ix) 0 = ix i := by
    show ix (0 + i) = ix i
    rw [zero_add]
  rw [← h0, rootedCol_constList_cycle hk _ hrot, rootedCol_constList_cycle hk ix hadj]

/-- **The balanced fibre product**: if a family `S` of proper colourings uses every colour of
`L v` exactly `F` times at `v`, then the weights it accumulates at `v` are exactly the list
product raised to `F`. This is the combinatorial half of the balanced-core route (UM-025 ⟹
UM-026): it is what makes the `F`-th roots cancel in the rooted bound. -/
theorem prod_of_balanced {F : ℕ} (L : ListAssignment V) (w : V → ℕ → ℕ)
    (S : Finset (V → ℕ)) (hS : S ⊆ G.colorings L)
    (hbal : ∀ v, ∀ c ∈ L v, (S.filter (fun f => f v = c)).card = F) (v : V) :
    ∏ f ∈ S, w v (f v) = ∏ c ∈ L v, (w v c) ^ F := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := fun f : V → ℕ => f v) (t := L v)
    (fun f hf => G.mem_list_of_mem_colorings (hS hf) v) (fun f => w v (f v))]
  refine Finset.prod_congr rfl fun c hc => ?_
  rw [Finset.prod_congr rfl (fun f hf => by rw [(Finset.mem_filter.mp hf).2]),
    Finset.prod_const, hbal v c hc]

/-- **The balanced-core bound** (UM-025 ⟹ UM-026, in rooted form): a family of proper colourings
using every colour of every list exactly `F` times forces the GM invariant with normalizer `F`.
Fibre by fibre this is AM–GM; `prod_of_balanced` makes the `F`-th roots cancel, so the rooted
product bound comes out with no root surviving. -/
theorem gm_bound_of_balanced {k F : ℕ} (hF : 0 < F) (L : ListAssignment V)
    (hL : IsNListAssignment L k) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ k ≤ ∏ c ∈ L v, w v c)
    (S : Finset (V → ℕ)) (hS : S ⊆ G.colorings L)
    (hbal : ∀ v, ∀ c ∈ L v, (S.filter (fun f => f v = c)).card = F) (r : V) :
    (F * ∏ v, W v) ^ k ≤ ∏ c ∈ L r, rootedWcol G L w r c := by
  classical
  set x : (V → ℕ) → ℕ := fun f => ∏ v, w v (f v) with hxdef
  -- the total weight of the family, two ways
  have htot : ∏ f ∈ S, x f = ∏ v, ∏ c ∈ L v, (w v c) ^ F := by
    rw [hxdef, Finset.prod_comm]
    exact Finset.prod_congr rfl fun v _ => prod_of_balanced L w S hS hbal v
  -- each root fibre: AM–GM, against the rooted count
  have hfibre : ∀ c ∈ L r, F ^ F * ∏ f ∈ S.filter (fun f => f r = c), x f
      ≤ (rootedWcol G L w r c) ^ F := by
    intro c hc
    have hcard : (S.filter (fun f => f r = c)).card = F := hbal r c hc
    have hAM := card_pow_mul_prod_le_sum_pow_nat (S.filter (fun f => f r = c)) x
    rw [hcard] at hAM
    refine hAM.trans (Nat.pow_le_pow_left (Finset.sum_le_sum_of_subset ?_) F)
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨hS hf.1, hf.2⟩
  -- multiply the `k` fibres and take `F`-th roots
  have hkey : F ^ k * ∏ v, ∏ c ∈ L v, w v c ≤ ∏ c ∈ L r, rootedWcol G L w r c := by
    refine (Nat.pow_le_pow_iff_left (by omega : F ≠ 0)).mp ?_
    calc (F ^ k * ∏ v, ∏ c ∈ L v, w v c) ^ F
        = (F ^ F) ^ k * ∏ v, ∏ c ∈ L v, (w v c) ^ F := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm k F, pow_mul, ← Finset.prod_pow]
          congr 1
          exact Finset.prod_congr rfl fun v _ => (Finset.prod_pow (L v) F (w v)).symm
      _ = ∏ c ∈ L r, (F ^ F * ∏ f ∈ S.filter (fun f => f r = c), x f) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hL r,
            Finset.prod_fiberwise_of_maps_to
              (fun f hf => G.mem_list_of_mem_colorings (hS hf) r) x, htot]
      _ ≤ ∏ c ∈ L r, (rootedWcol G L w r c) ^ F :=
          Finset.prod_le_prod' (fun c hc => hfibre c hc)
      _ = (∏ c ∈ L r, rootedWcol G L w r c) ^ F := Finset.prod_pow _ _ _
  refine le_trans ?_ hkey
  calc (F * ∏ v, W v) ^ k = F ^ k * ∏ v, (W v) ^ k := by
        rw [mul_pow, Finset.prod_pow]
    _ ≤ F ^ k * ∏ v, ∏ c ∈ L v, w v c :=
        Nat.mul_le_mul_left _ (Finset.prod_le_prod' (fun v _ => hdom v))

end Balanced

section Induction

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The single-edge base** of the GM induction: on two adjacent vertices the rooted profile is
`c ↦ w r c · ∑_{e ≠ c} w x e`, and `pendant_gm_dominant` clears the uniform factor `2 ^ 3 = 8`. -/
theorem gm_edge_base (hcard : Fintype.card V = 2) (hG : IsCactus G)
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) (r : V) :
    (rootedCol G (constList V 3) r 0 * ∏ v, W v) ^ 3 ≤ ∏ c ∈ L r, rootedWcol G L w r c := by
  classical
  obtain ⟨x, hxr⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) r
  have hrx : r ≠ x := fun h => hxr h.symm
  have huniv : (Finset.univ : Finset V) = {r, x} := by
    refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
    rw [Finset.card_univ, hcard, Finset.card_insert_of_notMem (by simpa using hrx),
      Finset.card_singleton]
  have hcard1 : Fintype.card {y : V // y ≠ x} = 1 := by
    have hcong := Fintype.card_congr (delOptionEquiv x)
    rw [Fintype.card_option] at hcong
    omega
  -- the two vertices are adjacent, and `x` is a pendant with neighbour `r`
  have hxu : G.Adj x r := by
    obtain ⟨Wk⟩ := hG.1.preconnected x r
    have hnil : ¬ Wk.Nil := Walk.not_nil_of_ne hxr
    have hadj := Wk.adj_snd hnil
    have hmem : Wk.snd ∈ ({r, x} : Finset V) := huniv ▸ Finset.mem_univ _
    rcases Finset.mem_insert.mp hmem with h | h
    · rwa [h] at hadj
    · rw [Finset.mem_singleton] at h
      exact absurd (h ▸ hadj) (G.irrefl)
  have huniq : ∀ y, G.Adj x y → y = r := by
    intro y hy
    have hmem : y ∈ ({r, x} : Finset V) := huniv ▸ Finset.mem_univ _
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · rw [Finset.mem_singleton] at h
      exact absurd (h ▸ hy) (G.irrefl)
  -- the rooted profile of an edge, and its uniform count
  have hprof : ∀ c ∈ L r, rootedWcol G L w r c
      = w r c * ∑ e ∈ (L x).filter (· ≠ c), w x e := by
    intro c hc
    rw [rootedWcol_pendant hxu huniq hrx L w c,
      rootedWcol_of_card_eq_one hcard1 _ _ ⟨r, hrx⟩ hc]
    simp
  have hA : rootedCol G (constList V 3) r 0 = 2 := by
    have h0 : (0 : ℕ) ∈ constList V 3 (⟨r, hrx⟩ : {y : V // y ≠ x}).val := by
      simp [constList_apply, Finset.mem_range]
    have hone := rootedWcol_of_card_eq_one (G := G.induce {y : V | y ≠ x}) hcard1
      (fun v => constList V 3 v.val) (fun _ _ => 1) ⟨r, hrx⟩ h0
    rw [rootedWcol_one] at hone
    rw [rootedCol_pendant_uniform hxu huniq hrx (by omega : 1 ≤ 3) 0, hone]
  have hprodV : (∏ v, W v) = W r * W x := by
    rw [huniv, Finset.prod_insert (by simpa using hrx), Finset.prod_singleton]
  rw [hA, hprodV, Finset.prod_congr rfl hprof, Finset.prod_mul_distrib]
  calc (2 * (W r * W x)) ^ 3 = W r ^ 3 * (8 * W x ^ 3) := by ring
    _ ≤ (∏ c ∈ L r, w r c) * ∏ c ∈ L r, ∑ e ∈ (L x).filter (· ≠ c), w x e :=
        Nat.mul_le_mul (hdom r) (pendant_gm_dominant (hL x) (hL r) (w x) (hdom x))

end Induction

end ListColoring
