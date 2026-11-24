module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Step 4 of `(n = 15, d = 5)` Impossibility: No 5-Regular, Triangle-Free, Induced-`2K₂`-Free Graph on 14 Vertices

This self-contained graph-theoretic lemma completes the impossibility proof for
`(n = 15, d = 5)` (`B_5 ≤ 14`).

Given a symmetric irreflexive graph `G` on `Fin 14` that is:
1. `5`-regular,
2. triangle-free, and
3. induced-`2K₂`-free (every two disjoint edges have at least one edge between them),

fixing `v = 0` partitions the remaining vertices into `N = N(0)` (`|N| = 5`, independent)
and `M = V \ ({0} ∪ N)` (`|M| = 8`), with `e(N, M) = 20`. Any edge `xy` in `M` forces
`N = A ⊔ B` with `1 ≤ |A| ≤ 4`, partitions `M = X ⊔ Y ⊔ R` (`|X| + |Y| + |R| = 8`) with
`|X| ≥ a`, `|Y| ≥ b`, `|X| * b = |Y| * a`, and `e(M, N) = |X| * a + |Y| * b + 5 * |R| = 20`,
which has no integer solution (`e(M, N) ≥ 28 > 20`).
-/

namespace DegreeSensitivity

open scoped BigOperators

/-- There is no 5-regular, triangle-free, induced-`2K₂`-free simple graph on 14 vertices. -/
theorem no_5reg_trifree_2k2free_14 (adj : Fin 14 → Fin 14 → Bool)
    (hirrefl : ∀ u, adj u u = false)
    (hsymm : ∀ u v, adj u v = adj v u)
    (hreg : ∀ u, (Finset.univ.filter (fun w => adj u w = true)).card = 5)
    (htrifree : ∀ u v w, adj u v = true → adj v w = true → adj u w = false)
    (h2k2free : ∀ a b c d,
      a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      adj a b = true → adj c d = true →
      adj a c = true ∨ adj a d = true ∨ adj b c = true ∨ adj b d = true) :
    False := by
  classical
  let v : Fin 14 := 0
  let N : Finset (Fin 14) := Finset.univ.filter (fun u => adj v u = true)
  let M : Finset (Fin 14) := (Finset.univ.erase v) \ N
  have hv_not_N : v ∉ N := by simp [N, hirrefl]
  have hN_card : N.card = 5 := hreg v
  have hN_sub : N ⊆ Finset.univ.erase v := by
    intro u hu
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ u⟩
    intro huv; subst huv; exact hv_not_N hu
  have hM_card : M.card = 8 := by
    rw [Finset.card_sdiff_of_subset hN_sub, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin, hN_card]
  have hNM_disj : Disjoint N M := disjoint_sdiff_self_right
  have hv_not_M : v ∉ M := by simp [M]
  have hpart_V : ∀ w : Fin 14, w = v ∨ w ∈ N ∨ w ∈ M := by
    intro w
    by_cases hwv : w = v
    · exact Or.inl hwv
    · by_cases hwN : w ∈ N
      · exact Or.inr (Or.inl hwN)
      · right; right
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩, hwN⟩
  have hN_indep : ∀ u ∈ N, ∀ w ∈ N, adj u w = false := by
    intro u hu w hw
    exact htrifree u v w (by rw [hsymm]; exact (Finset.mem_filter.mp hu).2)
      (Finset.mem_filter.mp hw).2
  have hv_no_M : ∀ w ∈ M, adj v w = false := by
    intro w hw
    have hw_not_N : w ∉ N := (Finset.mem_sdiff.mp hw).2
    cases hvw : adj v w
    · rfl
    · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hvw⟩) hw_not_N
  -- Helper: neighbors of `w` inside a finset `S`.
  let nbrs (w : Fin 14) (S : Finset (Fin 14)) : Finset (Fin 14) :=
    S.filter (fun u => adj w u = true)
  -- For any `w ∈ M`, `w`'s 5 neighbors split cleanly into `nbrs w N` and `nbrs w M`.
  have hM_deg_split : ∀ w ∈ M, (nbrs w N).card + (nbrs w M).card = 5 := by
    intro w hw
    have hdisj : Disjoint (nbrs w N) (nbrs w M) :=
      hNM_disj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [← Finset.card_union_of_disjoint hdisj]
    have heq : nbrs w N ∪ nbrs w M = Finset.univ.filter (fun u => adj w u = true) := by
      ext u
      simp only [nbrs, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
      · intro hwu
        rcases hpart_V u with rfl | huN | huM
        · exfalso
          rw [hsymm, hv_no_M w hw] at hwu
          exact Bool.false_ne_true hwu
        · exact Or.inl ⟨huN, hwu⟩
        · exact Or.inr ⟨huM, hwu⟩
    rw [heq, hreg w]
  -- For any `u ∈ N`, `u` has exactly 4 neighbors in `M` (its 5th neighbor is `v`, none in `N`).
  have hN_deg_M : ∀ u ∈ N, (nbrs u M).card = 4 := by
    intro u hu
    have hvu : adj u v = true := by rw [hsymm]; exact (Finset.mem_filter.mp hu).2
    have hv_mem : v ∈ Finset.univ.filter (fun w => adj u w = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvu⟩
    have heq : nbrs u M = (Finset.univ.filter (fun w => adj u w = true)).erase v := by
      ext w
      simp only [nbrs, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hwM, huw⟩
        exact ⟨fun hwv => hv_not_M (hwv ▸ hwM), huw⟩
      · rintro ⟨hwv, huw⟩
        refine ⟨?_, huw⟩
        rcases hpart_V w with rfl | hwN | hwM
        · exact absurd rfl hwv
        · rw [hN_indep u hu w hwN] at huw; exact absurd huw Bool.false_ne_true
        · exact hwM
    rw [heq, Finset.card_erase_of_mem hv_mem, hreg u]
  -- Double counting edges between `N` and `M`: `∑ w ∈ M, |nbrs w N| = 20`.
  have heNM : ∑ w ∈ M, (nbrs w N).card = 20 := by
    have h1 : ∑ w ∈ M, (nbrs w N).card = ∑ w ∈ M, ∑ u ∈ N, if adj w u = true then 1 else 0 := by
      apply Finset.sum_congr rfl; intro w _; simp [nbrs, Finset.sum_boole]
    have h2 : ∑ u ∈ N, (nbrs u M).card = ∑ u ∈ N, ∑ w ∈ M, if adj u w = true then 1 else 0 := by
      apply Finset.sum_congr rfl; intro u _; simp [nbrs, Finset.sum_boole]
    have hswap : ∑ w ∈ M, (nbrs w N).card = ∑ u ∈ N, (nbrs u M).card := by
      rw [h1, h2, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro w _
      rw [hsymm]
    rw [hswap]
    calc ∑ u ∈ N, (nbrs u M).card = ∑ _u ∈ N, 4 := Finset.sum_congr rfl hN_deg_M
      _ = 20 := by rw [Finset.sum_const, hN_card]; rfl
  -- Key property of ANY edge `w z` inside `M`: `nbrs w N` and `nbrs z N` partition `N`,
  -- and both have size in `[1, 4]`.
  have hedge_part : ∀ w ∈ M, ∀ z ∈ M, adj w z = true →
      Disjoint (nbrs w N) (nbrs z N) ∧ nbrs w N ∪ nbrs z N = N ∧
      1 ≤ (nbrs w N).card ∧ (nbrs w N).card ≤ 4 := by
    intro w hw z hz hwz
    have hdisj : Disjoint (nbrs w N) (nbrs z N) := by
      rw [Finset.disjoint_left]
      intro u huw huz
      have h1 : adj w u = true := (Finset.mem_filter.mp huw).2
      have h2 : adj z u = true := (Finset.mem_filter.mp huz).2
      have h3 := htrifree w z u hwz h2
      rw [h1] at h3; exact Bool.noConfusion h3
    have hunion : nbrs w N ∪ nbrs z N = N := by
      ext u
      simp only [nbrs, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨huN, _⟩ | ⟨huN, _⟩) <;> exact huN
      · intro huN
        have hvu : adj v u = true := (Finset.mem_filter.mp huN).2
        have hvw : v ≠ w := fun h => hv_not_M (h ▸ hw)
        have hvz : v ≠ z := fun h => hv_not_M (h ▸ hz)
        have huw : u ≠ w := fun h => Finset.disjoint_left.mp hNM_disj huN (h ▸ hw)
        have huz : u ≠ z := fun h => Finset.disjoint_left.mp hNM_disj huN (h ▸ hz)
        have h4 := h2k2free v u w z hvw hvz huw huz hvu hwz
        rcases h4 with h | h | h | h
        · rw [hv_no_M w hw] at h; exact absurd h Bool.false_ne_true
        · rw [hv_no_M z hz] at h; exact absurd h Bool.false_ne_true
        · exact Or.inl ⟨huN, by rw [hsymm]; exact h⟩
        · exact Or.inr ⟨huN, by rw [hsymm]; exact h⟩
    have hcard_sum : (nbrs w N).card + (nbrs z N).card = 5 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, hN_card]
    have hwM_pos : 1 ≤ (nbrs w M).card :=
      Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hwz⟩⟩
    have hzM_pos : 1 ≤ (nbrs z M).card :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, by rw [hsymm]; exact hwz⟩⟩
    have hws := hM_deg_split w hw
    have hzs := hM_deg_split z hz
    refine ⟨hdisj, hunion, by omega, by omega⟩
  -- Check whether `G[M]` has any edge at all.
  by_cases hM_edge : ∃ x ∈ M, ∃ y ∈ M, adj x y = true
  · obtain ⟨x, hxM, y, hyM, hxy⟩ := hM_edge
    let A := nbrs x N
    let B := nbrs y N
    obtain ⟨hAB_disj, hAB_union, ha1, ha4⟩ := hedge_part x hxM y hyM hxy
    set a := A.card with ha_def
    set b := B.card with hb_def
    have hab : a + b = 5 := by
      rw [ha_def, hb_def, ← Finset.card_union_of_disjoint hAB_disj, hAB_union, hN_card]
    -- Every non-isolated vertex in `M` has neighborhood in `N` equal to `A` or `B`!
    have hnoniso : ∀ w ∈ M, (nbrs w M).card ≠ 0 → nbrs w N = A ∨ nbrs w N = B := by
      intro w hwM hne0
      obtain ⟨z, hz⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne0)
      obtain ⟨hzM, hwz⟩ := Finset.mem_filter.mp hz
      obtain ⟨hwz_disj, hwz_union, _, _⟩ := hedge_part w hwM z hzM hwz
      -- Helper: if `u ~ y` (with `u ∈ M`), then `nbrs u N = A`; if `u ~ x`, then `nbrs u N = B`.
      have hadj_y : ∀ u ∈ M, adj u y = true → nbrs u N = A := by
        intro u huM huy
        obtain ⟨huy_disj, huy_union, _, _⟩ := hedge_part u huM y hyM huy
        ext t
        constructor
        · intro ht
          have htN : t ∈ N := (Finset.mem_filter.mp ht).1
          have ht_not_B : t ∉ B := Finset.disjoint_left.mp huy_disj ht
          rw [← hAB_union, Finset.mem_union] at htN
          exact htN.resolve_right ht_not_B
        · intro htA
          have htN : t ∈ N := (Finset.mem_filter.mp htA).1
          have ht_not_B : t ∉ B := Finset.disjoint_left.mp hAB_disj htA
          rw [← huy_union, Finset.mem_union] at htN
          exact htN.resolve_right ht_not_B
      have hadj_x : ∀ u ∈ M, adj u x = true → nbrs u N = B := by
        intro u huM hux
        obtain ⟨hux_disj, hux_union, _, _⟩ := hedge_part u huM x hxM hux
        ext t
        constructor
        · intro ht
          have htN : t ∈ N := (Finset.mem_filter.mp ht).1
          have ht_not_A : t ∉ A := Finset.disjoint_left.mp hux_disj ht
          rw [← hAB_union, Finset.mem_union] at htN
          exact htN.resolve_left ht_not_A
        · intro htB
          have htN : t ∈ N := (Finset.mem_filter.mp htB).1
          have ht_not_A : t ∉ A := Finset.disjoint_right.mp hAB_disj htB
          rw [← hux_union, Finset.mem_union] at htN
          exact htN.resolve_right ht_not_A
      have hcomp_of_z : (nbrs z N = A → nbrs w N = B) ∧ (nbrs z N = B → nbrs w N = A) := by
        constructor
        · intro hzA
          ext t
          constructor
          · intro ht
            have htN : t ∈ N := (Finset.mem_filter.mp ht).1
            have ht_not_A : t ∉ A := by rw [← hzA]; exact Finset.disjoint_left.mp hwz_disj ht
            rw [← hAB_union, Finset.mem_union] at htN
            exact htN.resolve_left ht_not_A
          · intro htB
            have htN : t ∈ N := (Finset.mem_filter.mp htB).1
            have ht_not_A : t ∉ A := Finset.disjoint_right.mp hAB_disj htB
            rw [← hwz_union, Finset.mem_union, hzA] at htN
            exact htN.resolve_right ht_not_A
        · intro hzB
          ext t
          constructor
          · intro ht
            have htN : t ∈ N := (Finset.mem_filter.mp ht).1
            have ht_not_B : t ∉ B := by rw [← hzB]; exact Finset.disjoint_left.mp hwz_disj ht
            rw [← hAB_union, Finset.mem_union] at htN
            exact htN.resolve_right ht_not_B
          · intro htA
            have htN : t ∈ N := (Finset.mem_filter.mp htA).1
            have ht_not_B : t ∉ B := Finset.disjoint_left.mp hAB_disj htA
            rw [← hwz_union, Finset.mem_union, hzB] at htN
            exact htN.resolve_right ht_not_B
      by_cases hwx : w = x
      · left; rw [hwx]
      · by_cases hwy : w = y
        · right; rw [hwy]
        · by_cases hzx : z = x
          · right; exact hadj_x w hwM (hzx ▸ hwz)
          · by_cases hzy : z = y
            · left; exact hadj_y w hwM (hzy ▸ hwz)
            · have h4 := h2k2free w z x y hwx hwy hzx hzy hwz hxy
              rcases h4 with h | h | h | h
              · right; exact hadj_x w hwM h
              · left; exact hadj_y w hwM h
              · left; exact hcomp_of_z.2 (hadj_x z hzM h)
              · right; exact hcomp_of_z.1 (hadj_y z hzM h)
    -- Partition `M` into `X`, `Y`, `R`.
    let X : Finset (Fin 14) := M.filter (fun w => nbrs w N = A)
    let Y : Finset (Fin 14) := M.filter (fun w => nbrs w N = B)
    let R : Finset (Fin 14) := M.filter (fun w => (nbrs w M).card = 0)
    have hAB_ne : A ≠ B := by
      intro hEq
      have hemp : A = ∅ := by
        ext t; simp only [Finset.notMem_empty, iff_false]
        intro ht
        have htB : t ∈ B := hEq ▸ ht
        exact Finset.disjoint_left.mp hAB_disj ht htB
      have ha0 : a = 0 := by rw [ha_def, hemp, Finset.card_empty]
      omega
    have hXY_disj : Disjoint X Y := by
      rw [Finset.disjoint_left]; intro w hwX hwY
      exact hAB_ne ((Finset.mem_filter.mp hwX).2.symm.trans (Finset.mem_filter.mp hwY).2)
    have hXR_disj : Disjoint X R := by
      rw [Finset.disjoint_left]; intro w hwX hwR
      have h1 := hM_deg_split w (Finset.mem_filter.mp hwX).1
      have h2 := (Finset.mem_filter.mp hwX).2
      have h3 := (Finset.mem_filter.mp hwR).2
      rw [h2, h3] at h1; omega
    have hYR_disj : Disjoint Y R := by
      rw [Finset.disjoint_left]; intro w hwY hwR
      have h1 := hM_deg_split w (Finset.mem_filter.mp hwY).1
      have h2 := (Finset.mem_filter.mp hwY).2
      have h3 := (Finset.mem_filter.mp hwR).2
      rw [h2, h3] at h1; omega
    have hM_union : M = X ∪ Y ∪ R := by
      ext w
      simp only [X, Y, R, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hwM
        by_cases h0 : (nbrs w M).card = 0
        · exact Or.inr ⟨hwM, h0⟩
        · rcases hnoniso w hwM h0 with hA | hB
          · exact Or.inl (Or.inl ⟨hwM, hA⟩)
          · exact Or.inl (Or.inr ⟨hwM, hB⟩)
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    have hcard_part : X.card + Y.card + R.card = 8 := by
      have hdisj1 : Disjoint (X ∪ Y) R := Finset.disjoint_union_left.mpr ⟨hXR_disj, hYR_disj⟩
      calc X.card + Y.card + R.card
          = (X ∪ Y).card + R.card := by rw [Finset.card_union_of_disjoint hXY_disj]
        _ = (X ∪ Y ∪ R).card := (Finset.card_union_of_disjoint hdisj1).symm
        _ = M.card := by rw [← hM_union]
        _ = 8 := hM_card
    -- Every neighbor in `M` of `w ∈ X` lies in `Y` (and vice versa).
    have hX_nbrs_Y : ∀ w ∈ X, nbrs w M = nbrs w Y := by
      intro w hwX
      have hwM := (Finset.mem_filter.mp hwX).1
      have hwA : nbrs w N = A := (Finset.mem_filter.mp hwX).2
      ext z
      simp only [nbrs, Finset.mem_filter]
      constructor
      · rintro ⟨hzM, hwz⟩
        refine ⟨Finset.mem_filter.mpr ⟨hzM, ?_⟩, hwz⟩
        have hz_ne0 : (nbrs z M).card ≠ 0 :=
          (Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hwM, by rw [hsymm]; exact hwz⟩⟩).ne'
        rcases hnoniso z hzM hz_ne0 with hzA | hzB
        · exfalso
          obtain ⟨hdisj, _, _, _⟩ := hedge_part w hwM z hzM hwz
          rw [hwA, hzA] at hdisj
          obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
          exact Finset.disjoint_left.mp hdisj ht ht
        · exact hzB
      · rintro ⟨hzY, hwz⟩
        exact ⟨(Finset.mem_filter.mp hzY).1, hwz⟩
    have hY_nbrs_X : ∀ w ∈ Y, nbrs w M = nbrs w X := by
      intro w hwY
      have hwM := (Finset.mem_filter.mp hwY).1
      have hwB : nbrs w N = B := (Finset.mem_filter.mp hwY).2
      ext z
      simp only [nbrs, Finset.mem_filter]
      constructor
      · rintro ⟨hzM, hwz⟩
        refine ⟨Finset.mem_filter.mpr ⟨hzM, ?_⟩, hwz⟩
        have hz_ne0 : (nbrs z M).card ≠ 0 :=
          (Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hwM, by rw [hsymm]; exact hwz⟩⟩).ne'
        rcases hnoniso z hzM hz_ne0 with hzA | hzB
        · exact hzA
        · exfalso
          obtain ⟨hdisj, _, _, _⟩ := hedge_part w hwM z hzM hwz
          rw [hwB, hzB] at hdisj
          obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
          exact Finset.disjoint_left.mp hdisj ht ht
      · rintro ⟨hzX, hwz⟩
        exact ⟨(Finset.mem_filter.mp hzX).1, hwz⟩
    -- Bounds `b ≤ Y.card` and `a ≤ X.card` from `x ∈ X` and `y ∈ Y`.
    have hY_ge_b : b ≤ Y.card := by
      have hxX : x ∈ X := Finset.mem_filter.mpr ⟨hxM, rfl⟩
      have hdeg := hM_deg_split x hxM
      change a + (nbrs x M).card = 5 at hdeg
      have hcard : (nbrs x Y).card = b := by rw [← hX_nbrs_Y x hxX]; omega
      rw [← hcard]; exact Finset.card_filter_le Y _
    have hX_ge_a : a ≤ X.card := by
      have hyY : y ∈ Y := Finset.mem_filter.mpr ⟨hyM, rfl⟩
      have hdeg := hM_deg_split y hyM
      change b + (nbrs y M).card = 5 at hdeg
      have hcard : (nbrs y X).card = a := by rw [← hY_nbrs_X y hyY]; omega
      rw [← hcard]; exact Finset.card_filter_le X _
    -- Double-counting edges between `X` and `Y`: `X.card * b = Y.card * a`.
    have heXY : X.card * b = Y.card * a := by
      have hlhs : ∑ w ∈ X, (nbrs w Y).card = X.card * b := by
        calc ∑ w ∈ X, (nbrs w Y).card
            = ∑ _w ∈ X, b := by
              apply Finset.sum_congr rfl
              intro w hwX
              have h1 := hM_deg_split w (Finset.mem_filter.mp hwX).1
              have h2 := (Finset.mem_filter.mp hwX).2
              rw [← hX_nbrs_Y w hwX]
              rw [h2] at h1; omega
          _ = X.card * b := by rw [Finset.sum_const]; rfl
      have hrhs : ∑ z ∈ Y, (nbrs z X).card = Y.card * a := by
        calc ∑ z ∈ Y, (nbrs z X).card
            = ∑ _z ∈ Y, a := by
              apply Finset.sum_congr rfl
              intro z hzY
              have h1 := hM_deg_split z (Finset.mem_filter.mp hzY).1
              have h2 := (Finset.mem_filter.mp hzY).2
              rw [← hY_nbrs_X z hzY]
              rw [h2] at h1; omega
          _ = Y.card * a := by rw [Finset.sum_const]; rfl
      rw [← hlhs, ← hrhs]
      have h1 : ∑ w ∈ X, (nbrs w Y).card = ∑ w ∈ X, ∑ z ∈ Y, if adj w z = true then 1 else 0 := by
        apply Finset.sum_congr rfl; intro w _; simp [nbrs, Finset.sum_boole]
      have h2 : ∑ z ∈ Y, (nbrs z X).card = ∑ z ∈ Y, ∑ w ∈ X, if adj z w = true then 1 else 0 := by
        apply Finset.sum_congr rfl; intro z _; simp [nbrs, Finset.sum_boole]
      rw [h1, h2, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro z _
      apply Finset.sum_congr rfl; intro w _
      rw [hsymm]
    -- Count `e(M, N) = X.card * a + Y.card * b + R.card * 5 = 20`.
    have heMN_part : X.card * a + Y.card * b + R.card * 5 = 20 := by
      have hdisj1 : Disjoint (X ∪ Y) R := Finset.disjoint_union_left.mpr ⟨hXR_disj, hYR_disj⟩
      rw [← heNM, hM_union, Finset.sum_union hdisj1, Finset.sum_union hXY_disj]
      have sX : ∑ w ∈ X, (nbrs w N).card = X.card * a := by
        calc ∑ w ∈ X, (nbrs w N).card = ∑ _w ∈ X, a :=
              Finset.sum_congr rfl (fun w hwX => by rw [(Finset.mem_filter.mp hwX).2])
          _ = X.card * a := by rw [Finset.sum_const]; rfl
      have sY : ∑ w ∈ Y, (nbrs w N).card = Y.card * b := by
        calc ∑ w ∈ Y, (nbrs w N).card = ∑ _w ∈ Y, b :=
              Finset.sum_congr rfl (fun w hwY => by rw [(Finset.mem_filter.mp hwY).2])
          _ = Y.card * b := by rw [Finset.sum_const]; rfl
      have sR : ∑ w ∈ R, (nbrs w N).card = R.card * 5 := by
        calc ∑ w ∈ R, (nbrs w N).card = ∑ _w ∈ R, 5 := by
              apply Finset.sum_congr rfl
              intro w hwR
              have h1 := hM_deg_split w (Finset.mem_filter.mp hwR).1
              have h2 := (Finset.mem_filter.mp hwR).2
              omega
          _ = R.card * 5 := by rw [Finset.sum_const]; rfl
      rw [sX, sY, sR]
    -- Arithmetic contradiction: `a ∈ {1, 2, 3, 4}`, `b = 5 - a`, `X ≥ a`, `Y ≥ b`,
    -- `X + Y + R = 8`, `X * b = Y * a`, `X * a + Y * b + 5 * R = 20` is impossible!
    have hcases : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
    rcases hcases with ha | ha | ha | ha
    · have hb : b = 4 := by omega
      rw [ha] at heXY heMN_part hX_ge_a; rw [hb] at heXY heMN_part hY_ge_b; omega
    · have hb : b = 3 := by omega
      rw [ha] at heXY heMN_part hX_ge_a; rw [hb] at heXY heMN_part hY_ge_b; omega
    · have hb : b = 2 := by omega
      rw [ha] at heXY heMN_part hX_ge_a; rw [hb] at heXY heMN_part hY_ge_b; omega
    · have hb : b = 1 := by omega
      rw [ha] at heXY heMN_part hX_ge_a; rw [hb] at heXY heMN_part hY_ge_b; omega
  · -- No edges inside `M`: every `w ∈ M` has all 5 neighbors in `N`, so `e(M, N) = 40 ≠ 20`!
    push Not at hM_edge
    have h40 : ∑ w ∈ M, (nbrs w N).card = 40 := by
      calc ∑ w ∈ M, (nbrs w N).card
          = ∑ _w ∈ M, 5 := by
            apply Finset.sum_congr rfl
            intro w hwM
            have h0 : (nbrs w M).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro z hzM hwz
              exact hM_edge w hwM z hzM hwz
            have := hM_deg_split w hwM
            omega
        _ = 40 := by rw [Finset.sum_const, hM_card]; rfl
    omega

end DegreeSensitivity
