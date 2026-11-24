module

public import DegreeSensitivity.IntTrieVerifier

@[expose] public section

/-!
# Terwilliger PSD Matrix Nonnegativity & 2-Stage Binomial-Basis PSD Verifier

This module establishes the elementary sum-of-squares nonnegativity of the Terwilliger block
matrices `B̃^(k)` for every `n, k : ℕ` with `2 * k ≤ n`:

  `0 ≤ ∑_{r, c = 0}^{n - 2k} w_r w_c ∑_b pairCount (n - 2k) r c b ∑_{a=0}^k (-1)^{k-a} C(k, a) m(k+r, k+c, a+b)`

via a completely elementary induction on `k`:
- **Base `k = 0`**: equals `(∑_r w_r S_r)^2 ≥ 0`.
- **Step `k → k + 1`**: averaging over all `(m + 2)(m + 1)` ordered pairs of distinct coordinates
  `(u, u.succAbove v)` of the antisymmetrized restriction
  `g_{u, v}(z) = g(z|_{u=1, v=0}) - g(z|_{u=0, v=1})` applies the finite difference
  `m(i+1, j+1, t+1) - m(i+1, j+1, t)` to `pairCorrR`, and Pascal's identity elevates `Δ^k` to `Δ^{k+1}`.

Using this theorem, we build the **2-stage `mTrie → cTrie` Binomial-Basis + PSD Verifier**
(`checkPsdBinoFarkas` and `checkPsdBinoBound`) powering Step 3 of the `B_6 ≤ 20` world record.
-/

namespace DegreeSensitivity

open scoped BigOperators

/-! ### Part 1: Real Pair Correlations & Inductive SOS Proof of `0 ≤ w^T B̃^(k) w` -/

/-- Pair correlation for an arbitrary real-valued function `g : (Fin n → Bool) → ℝ`. -/
noncomputable def pairCorrR {n : ℕ} (g : (Fin n → Bool) → ℝ) (i j t : ℕ) : ℝ :=
  (∑ p ∈ pairSet n i j t, g p.1 * g p.2) / (pairCount n i j t : ℝ)

lemma pairCorrR_bool {n i j t : ℕ} (f : BooleanFun n) :
    pairCorrR (fun x => boolToReal (f x)) i j t = pairCorr f i j t := rfl

/-- Entry `(r, c)` of the scaled Terwilliger PSD matrix `B̃^(k)` for `g : (Fin n → Bool) → ℝ`. -/
noncomputable def bTilde {n : ℕ} (k : ℕ) (g : (Fin n → Bool) → ℝ) (r c : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc (r + c - (n - 2 * k)) (min r c),
    (pairCount (n - 2 * k) r c b : ℝ) *
      ∑ a ∈ Finset.range (k + 1),
        (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
          pairCorrR g (k + r) (k + c) (a + b)

/-- Insert two bits `(b1, b2)` into `z : Fin m → Bool` at distinct positions `(u, u.succAbove v)`. -/
def insertTwo {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1)) (b1 b2 : Bool) (z : Fin m → Bool) :
    Fin (m + 2) → Bool :=
  u.insertNth b1 (v.insertNth b2 z)

/-- Remove positions `u` and `v` from `x : Fin (m + 2) → Bool`. -/
def removeTwo {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1)) (x : Fin (m + 2) → Bool) :
    Fin m → Bool :=
  v.removeNth (u.removeNth x)

private lemma insertTwo_apply_first {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1))
    (b1 b2 : Bool) (z : Fin m → Bool) :
    insertTwo u v b1 b2 z u = b1 := by
  simp [insertTwo]

private lemma insertTwo_apply_second {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1))
    (b1 b2 : Bool) (z : Fin m → Bool) :
    insertTwo u v b1 b2 z (u.succAbove v) = b2 := by
  simp [insertTwo]

private lemma removeTwo_insertTwo {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1))
    (b1 b2 : Bool) (z : Fin m → Bool) :
    removeTwo u v (insertTwo u v b1 b2 z) = z := by
  unfold removeTwo insertTwo
  funext k
  simp [Fin.removeNth]

private lemma insertTwo_removeTwo {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1))
    (b1 b2 : Bool) (x : Fin (m + 2) → Bool)
    (h1 : x u = b1) (h2 : x (u.succAbove v) = b2) :
    insertTwo u v b1 b2 (removeTwo u v x) = x := by
  unfold insertTwo removeTwo
  funext k
  refine Fin.succAboveCases u ?_ ?_ k
  · simp [h1]
  · intro j
    simp only [Fin.insertNth_apply_succAbove]
    refine Fin.succAboveCases v ?_ ?_ j
    · simp [h2]
    · intro l; simp [Fin.removeNth]

private lemma supportOf_insertNth_true {m : ℕ} (i : Fin (m + 1)) (y : Fin m → Bool) :
    supportOf (i.insertNth true y) = insert i ((supportOf y).map (Fin.succAboveEmb i)) := by
  ext k
  simp only [mem_supportOf, Finset.mem_insert, Finset.mem_map, Fin.succAboveEmb_apply]
  refine Fin.succAboveCases i ?_ ?_ k
  · simp
  · intro j
    simp only [Fin.insertNth_apply_succAbove, Fin.succAbove_ne, false_or]
    constructor
    · intro h; exact ⟨j, h, rfl⟩
    · rintro ⟨a, ha, hEq⟩; rw [← Fin.succAbove_right_injective hEq]; exact ha

private lemma supportOf_insertNth_false' {m : ℕ} (i : Fin (m + 1)) (y : Fin m → Bool) :
    supportOf (i.insertNth false y) = (supportOf y).map (Fin.succAboveEmb i) := by
  ext k
  simp only [mem_supportOf, Finset.mem_map, Fin.succAboveEmb_apply]
  refine Fin.succAboveCases i ?_ ?_ k
  · simp [Fin.succAbove_ne]
  · intro j
    simp only [Fin.insertNth_apply_succAbove]
    constructor
    · intro h; exact ⟨j, h, rfl⟩
    · rintro ⟨a, ha, hEq⟩; rw [← Fin.succAbove_right_injective hEq]; exact ha

private lemma supportOf_insertTwo_tf {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1)) (z : Fin m → Bool) :
    supportOf (insertTwo u v true false z) =
      insert u (((supportOf z).map (Fin.succAboveEmb v)).map (Fin.succAboveEmb u)) := by
  unfold insertTwo
  rw [supportOf_insertNth_true, supportOf_insertNth_false']

private lemma supportOf_insertTwo_ft {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1)) (z : Fin m → Bool) :
    supportOf (insertTwo u v false true z) =
      insert (u.succAbove v) (((supportOf z).map (Fin.succAboveEmb v)).map (Fin.succAboveEmb u)) := by
  unfold insertTwo
  rw [supportOf_insertNth_false', supportOf_insertNth_true, Finset.map_insert, Fin.succAboveEmb_apply]

private lemma card_supportOf_insertTwo {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1))
    (b : Bool) (z : Fin m → Bool) :
    (supportOf (insertTwo u v b (!b) z)).card = (supportOf z).card + 1 := by
  cases b
  · simp only [Bool.not_false, supportOf_insertTwo_ft]
    have hnot : u.succAbove v ∉ ((supportOf z).map (Fin.succAboveEmb v)).map (Fin.succAboveEmb u) := by
      simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
      intro a ha hEq
      have hv : a = v := Fin.succAbove_right_injective hEq
      rw [hv] at ha
      rcases ha with ⟨c, _, hc⟩
      exact Fin.succAbove_ne v c hc
    rw [Finset.card_insert_of_notMem hnot, Finset.card_map, Finset.card_map]
  · simp only [Bool.not_true, supportOf_insertTwo_tf]
    have hnot : u ∉ ((supportOf z).map (Fin.succAboveEmb v)).map (Fin.succAboveEmb u) := by
      simp [Fin.succAbove_ne]
    rw [Finset.card_insert_of_notMem hnot, Finset.card_map, Finset.card_map]

private lemma card_inter_insertTwo_same {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1))
    (b : Bool) (x y : Fin m → Bool) :
    (supportOf (insertTwo u v b (!b) x) ∩ supportOf (insertTwo u v b (!b) y)).card =
      (supportOf x ∩ supportOf y).card + 1 := by
  have hinter : ∀ (e : Fin m ↪ Fin (m + 2)) (a : Fin (m + 2)),
      (∀ k, e k ≠ a) →
      (insert a ((supportOf x).map e) ∩ insert a ((supportOf y).map e)).card =
        (supportOf x ∩ supportOf y).card + 1 := by
    intro e a hne
    have h1 : insert a ((supportOf x).map e) ∩ insert a ((supportOf y).map e) =
        insert a ((supportOf x ∩ supportOf y).map e) := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_map]
      constructor
      · rintro ⟨rfl | ⟨c, hcx, rfl⟩, h2 | ⟨d, hdy, hcd⟩⟩
        · exact Or.inl rfl
        · exact absurd hcd (hne d)
        · exact absurd h2 (hne c)
        · have : d = c := e.injective hcd
          subst this; exact Or.inr ⟨d, ⟨hcx, hdy⟩, rfl⟩
      · rintro (rfl | ⟨c, ⟨hcx, hdy⟩, rfl⟩)
        · exact ⟨Or.inl rfl, Or.inl rfl⟩
        · exact ⟨Or.inr ⟨c, hcx, rfl⟩, Or.inr ⟨c, hdy, rfl⟩⟩
    have hnot : a ∉ (supportOf x ∩ supportOf y).map e := by
      simp only [Finset.mem_map, not_exists, not_and]; intro c _ hc; exact hne c hc
    rw [h1, Finset.card_insert_of_notMem hnot, Finset.card_map]
  let e : Fin m ↪ Fin (m + 2) := (Fin.succAboveEmb v).trans (Fin.succAboveEmb u)
  have hmap : ∀ z : Fin m → Bool,
      ((supportOf z).map (Fin.succAboveEmb v)).map (Fin.succAboveEmb u) = (supportOf z).map e := by
    intro z; simp [e, Finset.map_map]
  cases b
  · simp only [Bool.not_false, supportOf_insertTwo_ft, hmap]
    exact hinter e (u.succAbove v) (fun c h => Fin.succAbove_ne v c (Fin.succAbove_right_injective h))
  · simp only [Bool.not_true, supportOf_insertTwo_tf, hmap]
    exact hinter e u (fun c h => Fin.succAbove_ne u (v.succAbove c) h)

private lemma card_inter_insertTwo_opp {m : ℕ} (u : Fin (m + 2)) (v : Fin (m + 1))
    (b : Bool) (x y : Fin m → Bool) :
    (supportOf (insertTwo u v b (!b) x) ∩ supportOf (insertTwo u v (!b) b y)).card =
      (supportOf x ∩ supportOf y).card := by
  let e : Fin m ↪ Fin (m + 2) := (Fin.succAboveEmb v).trans (Fin.succAboveEmb u)
  have hmap : ∀ z : Fin m → Bool,
      ((supportOf z).map (Fin.succAboveEmb v)).map (Fin.succAboveEmb u) = (supportOf z).map e := by
    intro z; simp [e, Finset.map_map]
  have he_u : ∀ c, e c ≠ u := fun c h => Fin.succAbove_ne u (v.succAbove c) h
  have he_v : ∀ c, e c ≠ u.succAbove v := fun c h => Fin.succAbove_ne v c (Fin.succAbove_right_injective h)
  have huv : u ≠ u.succAbove v := (Fin.succAbove_ne u v).symm
  have hinter : ∀ (a₁ a₂ : Fin (m + 2)), a₁ ≠ a₂ → (∀ c, e c ≠ a₁) → (∀ c, e c ≠ a₂) →
      (insert a₁ ((supportOf x).map e) ∩ insert a₂ ((supportOf y).map e)).card =
        (supportOf x ∩ supportOf y).card := by
    intro a₁ a₂ hne h1 h2
    have heq : insert a₁ ((supportOf x).map e) ∩ insert a₂ ((supportOf y).map e) =
        (supportOf x ∩ supportOf y).map e := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_map]
      constructor
      · rintro ⟨rfl | ⟨c, hcx, rfl⟩, h2' | ⟨d, hdy, hcd⟩⟩
        · exact absurd h2' hne
        · exact absurd hcd (h1 d)
        · exact absurd h2' (h2 c)
        · have : d = c := e.injective hcd
          subst this; exact ⟨d, ⟨hcx, hdy⟩, rfl⟩
      · rintro ⟨c, ⟨hcx, hdy⟩, rfl⟩
        exact ⟨Or.inr ⟨c, hcx, rfl⟩, Or.inr ⟨c, hdy, rfl⟩⟩
    rw [heq, Finset.card_map]
  cases b
  · simp only [Bool.not_false, supportOf_insertTwo_ft, supportOf_insertTwo_tf, hmap]
    exact hinter (u.succAbove v) u huv.symm he_v he_u
  · simp only [Bool.not_true, supportOf_insertTwo_ft, supportOf_insertTwo_tf, hmap]
    exact hinter u (u.succAbove v) huv he_u he_v

/-- Helper: number of pairs `(u : Fin (m+2), v : Fin (m+1))` with `u ∈ A` and `u.succAbove v ∈ B`
for disjoint `A, B : Finset (Fin (m+2))` equals `A.card * B.card`. -/
private lemma card_disjoint_ordered_pairs {m : ℕ} (A B : Finset (Fin (m + 2))) (hdisj : Disjoint A B) :
    ((Finset.univ : Finset (Fin (m + 2) × Fin (m + 1))).filter
      (fun uv => uv.1 ∈ A ∧ uv.1.succAbove uv.2 ∈ B)).card = A.card * B.card := by
  have h1 : ((Finset.univ : Finset (Fin (m + 2) × Fin (m + 1))).filter
      (fun uv => uv.1 ∈ A ∧ uv.1.succAbove uv.2 ∈ B)).card =
      (A ×ˢ B).card := by
    apply Finset.card_bij (fun uv _ => (uv.1, uv.1.succAbove uv.2))
    · intro uv huv
      obtain ⟨_, hA, hB⟩ := Finset.mem_filter.mp huv
      exact Finset.mem_product.mpr ⟨hA, hB⟩
    · intro uv₁ _ uv₂ _ hEq
      obtain ⟨hu, hv_eq⟩ := Prod.mk.inj hEq
      rw [hu] at hv_eq
      exact Prod.ext hu (Fin.succAbove_right_injective hv_eq)
    · rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      have hne : b ≠ a := fun h => Finset.disjoint_left.mp hdisj ha (h ▸ hb)
      obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq hne
      refine ⟨(a, v), ?_, Prod.ext rfl hv⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ha, hv.symm ▸ hb⟩
  rw [h1, Finset.card_product]

/-- Fiberwise sum identity for `insertTwo` when both inputs use `(b, !b)` (same orientation). -/
private lemma sum_insertTwo_same {m i j t : ℕ} (g : (Fin (m + 2) → Bool) → ℝ) (b : Bool) :
    ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
      g (insertTwo u v b (!b) p.1) * g (insertTwo u v b (!b) p.2) =
    ((t + 1) * (m + t + 1 - i - j) : ℕ) *
      ∑ q ∈ pairSet (m + 2) (i + 1) (j + 1) (t + 1), g q.1 * g q.2 := by
  classical
  set S := (Finset.univ : Finset (Fin (m + 2) × Fin (m + 1))) ×ˢ pairSet m i j t
  set T := pairSet (m + 2) (i + 1) (j + 1) (t + 1)
  let Φ : (Fin (m + 2) × Fin (m + 1)) × ((Fin m → Bool) × (Fin m → Bool)) →
      (Fin (m + 2) → Bool) × (Fin (m + 2) → Bool) :=
    fun s => (insertTwo s.1.1 s.1.2 b (!b) s.2.1, insertTwo s.1.1 s.1.2 b (!b) s.2.2)
  have hmaps : ∀ s ∈ S, Φ s ∈ T := by
    rintro ⟨⟨u, v⟩, ⟨x, y⟩⟩ hs
    have hxy := (Finset.mem_product.mp hs).2
    simp only [T, pairSet, Finset.mem_filter, Finset.mem_product, hammingLayer, Finset.mem_univ,
      true_and] at hxy ⊢
    obtain ⟨⟨hx, hy⟩, hxy_t⟩ := hxy
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · dsimp only [Φ]; rw [card_supportOf_insertTwo, hx]
    · dsimp only [Φ]; rw [card_supportOf_insertTwo, hy]
    · dsimp only [Φ]; rw [card_inter_insertTwo_same, hxy_t]
  have hlhs : ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
      g (insertTwo u v b (!b) p.1) * g (insertTwo u v b (!b) p.2) =
      ∑ s ∈ S, g (Φ s).1 * g (Φ s).2 := by
    rw [Finset.sum_product, ← Finset.univ_product_univ, Finset.sum_product]
  rw [hlhs, ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hval : ∑ s ∈ S.filter (fun s => Φ s = q), g (Φ s).1 * g (Φ s).2 =
      ((S.filter (fun s => Φ s = q)).card : ℝ) * (g q.1 * g q.2) := by
    calc ∑ s ∈ S.filter (fun s => Φ s = q), g (Φ s).1 * g (Φ s).2
        = ∑ _s ∈ S.filter (fun s => Φ s = q), (g q.1 * g q.2) :=
          Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2])
      _ = ((S.filter (fun s => Φ s = q)).card : ℝ) * (g q.1 * g q.2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [hval]
  congr 1
  apply congrArg (Nat.cast : ℕ → ℝ)
  simp only [T, pairSet, Finset.mem_filter, Finset.mem_product, hammingLayer, Finset.mem_univ,
    true_and] at hq
  obtain ⟨⟨hq1, hq2⟩, hqt⟩ := hq
  -- Biject the fiber `S.filter (Φ s = q)` with `{uv | q.1 uv.1 = b ∧ q.2 uv.1 = b ∧ q.1 (uv.1.succAbove uv.2) = !b ∧ q.2 (uv.1.succAbove uv.2) = !b}`.
  set A1 := supportOf q.1 ∩ supportOf q.2
  set A0 := (supportOf q.1 ∪ supportOf q.2)ᶜ
  have hdisj : Disjoint A1 A0 := by
    rw [Finset.disjoint_left]; intro k hk1 hk0
    exact (Finset.mem_compl.mp hk0) (Finset.mem_union_left _ (Finset.mem_inter.mp hk1).1)
  have hA1 : A1.card = t + 1 := hqt
  have hA0 : A0.card = m + t + 1 - i - j := by
    have hu := Finset.card_union_add_card_inter (supportOf q.1) (supportOf q.2)
    rw [hq1, hq2, hqt] at hu
    rw [Finset.card_compl, Fintype.card_fin]
    have hule : (supportOf q.1 ∪ supportOf q.2).card ≤ m + 2 := by
      simpa using Finset.card_le_univ (supportOf q.1 ∪ supportOf q.2)
    omega
  have hfib_bij : (S.filter (fun s => Φ s = q)).card =
      ((Finset.univ : Finset (Fin (m + 2) × Fin (m + 1))).filter
        (fun uv => uv.1 ∈ (if b then A1 else A0) ∧ uv.1.succAbove uv.2 ∈ (if b then A0 else A1))).card := by
    apply Finset.card_bij (fun s _ => s.1)
    · rintro ⟨⟨u, v⟩, ⟨x, y⟩⟩ hs
      obtain ⟨_, hEq⟩ := Finset.mem_filter.mp hs
      have h1 : insertTwo u v b (!b) x = q.1 := congrArg Prod.fst hEq
      have h2 : insertTwo u v b (!b) y = q.2 := congrArg Prod.snd hEq
      have hq1u : q.1 u = b := by rw [← h1, insertTwo_apply_first]
      have hq2u : q.2 u = b := by rw [← h2, insertTwo_apply_first]
      have hq1v : q.1 (u.succAbove v) = !b := by rw [← h1, insertTwo_apply_second]
      have hq2v : q.2 (u.succAbove v) = !b := by rw [← h2, insertTwo_apply_second]
      rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · cases b <;> simp [A1, A0, mem_supportOf, hq1u, hq2u]
      · cases b <;> simp [A1, A0, mem_supportOf, hq1v, hq2v]
    · rintro ⟨⟨u₁, v₁⟩, ⟨x₁, y₁⟩⟩ hs₁ ⟨⟨u₂, v₂⟩, ⟨x₂, y₂⟩⟩ hs₂ huv
      dsimp only at huv
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp huv
      have hEq1 := (Finset.mem_filter.mp hs₁).2
      have hEq2 := (Finset.mem_filter.mp hs₂).2
      have hx : x₁ = x₂ := by
        have := congrArg (fun p => removeTwo u₁ v₁ p.1) (hEq1.trans hEq2.symm)
        simpa [Φ, removeTwo_insertTwo] using this
      have hy : y₁ = y₂ := by
        have := congrArg (fun p => removeTwo u₁ v₁ p.2) (hEq1.trans hEq2.symm)
        simpa [Φ, removeTwo_insertTwo] using this
      subst hx; subst hy; rfl
    · rintro ⟨u, v⟩ huv
      obtain ⟨_, hu_mem, hv_mem⟩ := Finset.mem_filter.mp huv
      have hq1u : q.1 u = b := by
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true, A1, A0, Finset.mem_inter,
          Finset.mem_compl, Finset.mem_union, mem_supportOf, not_or] at hu_mem
        · cases h : q.1 u; rfl; exact absurd h hu_mem.1
        · exact hu_mem.1
      have hq2u : q.2 u = b := by
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true, A1, A0, Finset.mem_inter,
          Finset.mem_compl, Finset.mem_union, mem_supportOf, not_or] at hu_mem
        · cases h : q.2 u; rfl; exact absurd h hu_mem.2
        · exact hu_mem.2
      have hq1v : q.1 (u.succAbove v) = !b := by
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true, A1, A0, Finset.mem_inter,
          Finset.mem_compl, Finset.mem_union, mem_supportOf, not_or] at hv_mem
        · exact hv_mem.1
        · cases h : q.1 (u.succAbove v); rfl; exact absurd h hv_mem.1
      have hq2v : q.2 (u.succAbove v) = !b := by
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true, A1, A0, Finset.mem_inter,
          Finset.mem_compl, Finset.mem_union, mem_supportOf, not_or] at hv_mem
        · exact hv_mem.2
        · cases h : q.2 (u.succAbove v); rfl; exact absurd h hv_mem.2
      let x := removeTwo u v q.1
      let y := removeTwo u v q.2
      have hrec1 : insertTwo u v b (!b) x = q.1 := insertTwo_removeTwo u v b (!b) q.1 hq1u hq1v
      have hrec2 : insertTwo u v b (!b) y = q.2 := insertTwo_removeTwo u v b (!b) q.2 hq2u hq2v
      refine ⟨((u, v), (x, y)), ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, Prod.ext hrec1 hrec2⟩
      simp only [pairSet, Finset.mem_filter, Finset.mem_product, hammingLayer, Finset.mem_univ,
        true_and]
      have hxcard : (supportOf x).card = i := by
        have := card_supportOf_insertTwo u v b x; rw [hrec1, hq1] at this; omega
      have hycard : (supportOf y).card = j := by
        have := card_supportOf_insertTwo u v b y; rw [hrec2, hq2] at this; omega
      have hinter : (supportOf x ∩ supportOf y).card = t := by
        have := card_inter_insertTwo_same u v b x y; rw [hrec1, hrec2, hqt] at this; omega
      exact ⟨⟨hxcard, hycard⟩, hinter⟩
  rw [hfib_bij]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [card_disjoint_ordered_pairs A0 A1 hdisj.symm, hA0, hA1, mul_comm]
  · simp only [↓reduceIte]
    rw [card_disjoint_ordered_pairs A1 A0 hdisj, hA1, hA0]

/-- Fiberwise sum identity for `insertTwo` when inputs use opposite orientations `(b, !b)` and `(!b, b)`. -/
private lemma sum_insertTwo_opp {m i j t : ℕ} (g : (Fin (m + 2) → Bool) → ℝ) (b : Bool) :
    ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
      g (insertTwo u v b (!b) p.1) * g (insertTwo u v (!b) b p.2) =
    ((i + 1 - t) * (j + 1 - t) : ℕ) *
      ∑ q ∈ pairSet (m + 2) (i + 1) (j + 1) t, g q.1 * g q.2 := by
  classical
  set S := (Finset.univ : Finset (Fin (m + 2) × Fin (m + 1))) ×ˢ pairSet m i j t
  set T := pairSet (m + 2) (i + 1) (j + 1) t
  let Φ : (Fin (m + 2) × Fin (m + 1)) × ((Fin m → Bool) × (Fin m → Bool)) →
      (Fin (m + 2) → Bool) × (Fin (m + 2) → Bool) :=
    fun s => (insertTwo s.1.1 s.1.2 b (!b) s.2.1, insertTwo s.1.1 s.1.2 (!b) b s.2.2)
  have hmaps : ∀ s ∈ S, Φ s ∈ T := by
    rintro ⟨⟨u, v⟩, ⟨x, y⟩⟩ hs
    have hxy := (Finset.mem_product.mp hs).2
    simp only [T, pairSet, Finset.mem_filter, Finset.mem_product, hammingLayer, Finset.mem_univ,
      true_and] at hxy ⊢
    obtain ⟨⟨hx, hy⟩, hxy_t⟩ := hxy
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · dsimp only [Φ]; rw [card_supportOf_insertTwo, hx]
    · dsimp only [Φ]
      have := card_supportOf_insertTwo u v (!b) y
      simp only [Bool.not_not] at this; rw [this, hy]
    · dsimp only [Φ]; rw [card_inter_insertTwo_opp, hxy_t]
  have hlhs : ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
      g (insertTwo u v b (!b) p.1) * g (insertTwo u v (!b) b p.2) =
      ∑ s ∈ S, g (Φ s).1 * g (Φ s).2 := by
    rw [Finset.sum_product, ← Finset.univ_product_univ, Finset.sum_product]
  rw [hlhs, ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hval : ∑ s ∈ S.filter (fun s => Φ s = q), g (Φ s).1 * g (Φ s).2 =
      ((S.filter (fun s => Φ s = q)).card : ℝ) * (g q.1 * g q.2) := by
    calc ∑ s ∈ S.filter (fun s => Φ s = q), g (Φ s).1 * g (Φ s).2
        = ∑ _s ∈ S.filter (fun s => Φ s = q), (g q.1 * g q.2) :=
          Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2])
      _ = ((S.filter (fun s => Φ s = q)).card : ℝ) * (g q.1 * g q.2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [hval]
  congr 1
  apply congrArg (Nat.cast : ℕ → ℝ)
  simp only [T, pairSet, Finset.mem_filter, Finset.mem_product, hammingLayer, Finset.mem_univ,
    true_and] at hq
  obtain ⟨⟨hq1, hq2⟩, hqt⟩ := hq
  set D1 := supportOf q.1 \ supportOf q.2
  set D2 := supportOf q.2 \ supportOf q.1
  have hdisj : Disjoint D1 D2 := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    exact (Finset.mem_sdiff.mp hk1).2 (Finset.mem_sdiff.mp hk2).1
  have hD1 : D1.card = i + 1 - t := by rw [Finset.card_sdiff, Finset.inter_comm, hq1, hqt]
  have hD2 : D2.card = j + 1 - t := by rw [Finset.card_sdiff, hq2, hqt]
  have hfib_bij : (S.filter (fun s => Φ s = q)).card =
      ((Finset.univ : Finset (Fin (m + 2) × Fin (m + 1))).filter
        (fun uv => uv.1 ∈ (if b then D1 else D2) ∧ uv.1.succAbove uv.2 ∈ (if b then D2 else D1))).card := by
    apply Finset.card_bij (fun s _ => s.1)
    · rintro ⟨⟨u, v⟩, ⟨x, y⟩⟩ hs
      obtain ⟨_, hEq⟩ := Finset.mem_filter.mp hs
      have h1 : insertTwo u v b (!b) x = q.1 := congrArg Prod.fst hEq
      have h2 : insertTwo u v (!b) b y = q.2 := congrArg Prod.snd hEq
      have hq1u : q.1 u = b := by rw [← h1, insertTwo_apply_first]
      have hq2u : q.2 u = !b := by rw [← h2, insertTwo_apply_first]
      have hq1v : q.1 (u.succAbove v) = !b := by rw [← h1, insertTwo_apply_second]
      have hq2v : q.2 (u.succAbove v) = b := by rw [← h2, insertTwo_apply_second]
      rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · cases b <;> simp [D1, D2, mem_supportOf, hq1u, hq2u]
      · cases b <;> simp [D1, D2, mem_supportOf, hq1v, hq2v]
    · rintro ⟨⟨u₁, v₁⟩, ⟨x₁, y₁⟩⟩ hs₁ ⟨⟨u₂, v₂⟩, ⟨x₂, y₂⟩⟩ hs₂ huv
      dsimp only at huv
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp huv
      have hEq1 := (Finset.mem_filter.mp hs₁).2
      have hEq2 := (Finset.mem_filter.mp hs₂).2
      have hx : x₁ = x₂ := by
        have := congrArg (fun p => removeTwo u₁ v₁ p.1) (hEq1.trans hEq2.symm)
        simpa [Φ, removeTwo_insertTwo] using this
      have hy : y₁ = y₂ := by
        have := congrArg (fun p => removeTwo u₁ v₁ p.2) (hEq1.trans hEq2.symm)
        simpa [Φ, removeTwo_insertTwo] using this
      subst hx; subst hy; rfl
    · rintro ⟨u, v⟩ huv
      obtain ⟨_, hu_mem, hv_mem⟩ := Finset.mem_filter.mp huv
      have hq1u : q.1 u = b := by
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true, D1, D2, Finset.mem_sdiff,
          mem_supportOf] at hu_mem
        · cases h : q.1 u; rfl; exact absurd h hu_mem.2
        · exact hu_mem.1
      have hq2u : q.2 u = !b := by
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true, D1, D2, Finset.mem_sdiff,
          mem_supportOf] at hu_mem
        · exact hu_mem.1
        · cases h : q.2 u; rfl; exact absurd h hu_mem.2
      have hq1v : q.1 (u.succAbove v) = !b := by
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true, D1, D2, Finset.mem_sdiff,
          mem_supportOf] at hv_mem
        · exact hv_mem.1
        · cases h : q.1 (u.succAbove v); rfl; exact absurd h hv_mem.2
      have hq2v : q.2 (u.succAbove v) = b := by
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true, D1, D2, Finset.mem_sdiff,
          mem_supportOf] at hv_mem
        · cases h : q.2 (u.succAbove v); rfl; exact absurd h hv_mem.2
        · exact hv_mem.1
      let x := removeTwo u v q.1
      let y := removeTwo u v q.2
      have hrec1 : insertTwo u v b (!b) x = q.1 := insertTwo_removeTwo u v b (!b) q.1 hq1u hq1v
      have hrec2 : insertTwo u v (!b) b y = q.2 := insertTwo_removeTwo u v (!b) b q.2 hq2u hq2v
      refine ⟨((u, v), (x, y)), ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, Prod.ext hrec1 hrec2⟩
      simp only [pairSet, Finset.mem_filter, Finset.mem_product, hammingLayer, Finset.mem_univ,
        true_and]
      have hxcard : (supportOf x).card = i := by
        have := card_supportOf_insertTwo u v b x; rw [hrec1, hq1] at this; omega
      have hycard : (supportOf y).card = j := by
        have := card_supportOf_insertTwo u v (!b) y
        simp only [Bool.not_not] at this; rw [hrec2, hq2] at this; omega
      have hinter : (supportOf x ∩ supportOf y).card = t := by
        have := card_inter_insertTwo_opp u v b x y; rw [hrec1, hrec2, hqt] at this; omega
      exact ⟨⟨hxcard, hycard⟩, hinter⟩
  rw [hfib_bij]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [card_disjoint_ordered_pairs D2 D1 hdisj.symm, hD1, hD2, mul_comm]
  · simp only [↓reduceIte]
    rw [card_disjoint_ordered_pairs D1 D2 hdisj, hD1, hD2]

/-- Elementary binomial absorption identity `(k + 1) * C(n + 1, k + 1) = (n + 1) * C(n, k)`. -/
private lemma choose_mul_eq (n : ℕ) :
    ∀ k : ℕ, (k + 1) * Nat.choose (n + 1) (k + 1) = (n + 1) * Nat.choose n k := by
  induction n with
  | zero =>
    intro k; cases k with
    | zero => decide
    | succ k => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < k + 2)]
  | succ n ih =>
    intro k; cases k with
    | zero => simp
    | succ k =>
      have h1 := ih k
      have h2 := ih (k + 1)
      calc (k + 1 + 1) * Nat.choose (n + 1 + 1) (k + 1 + 1)
          = (k + 1 + 1) * (Nat.choose (n + 1) (k + 1) + Nat.choose (n + 1) (k + 1 + 1)) := by
            rw [Nat.choose_succ_succ (n + 1) (k + 1)]
        _ = Nat.choose (n + 1) (k + 1) + (k + 1) * Nat.choose (n + 1) (k + 1) +
            (k + 1 + 1) * Nat.choose (n + 1) (k + 1 + 1) := by ring
        _ = Nat.choose (n + 1) (k + 1) + (n + 1) * Nat.choose n k +
            (n + 1) * Nat.choose n (k + 1) := by rw [h1, h2]
        _ = Nat.choose (n + 1) (k + 1) + (n + 1) * (Nat.choose n k + Nat.choose n (k + 1)) := by ring
        _ = Nat.choose (n + 1) (k + 1) + (n + 1) * Nat.choose (n + 1) (k + 1) := by
            rw [← Nat.choose_succ_succ n k]
        _ = (n + 1 + 1) * Nat.choose (n + 1) (k + 1) := by ring

private lemma pairCount_shift_same {m i j t : ℕ} (h : ValidTriple m i j t) :
    (t + 1) * (m + t + 1 - i - j) * pairCount (m + 2) (i + 1) (j + 1) (t + 1) =
      (m + 2) * (m + 1) * pairCount m i j t := by
  obtain ⟨hi, hj, hti, htj, hij⟩ := h
  unfold pairCount
  have h1 : (i + 1) * Nat.choose (m + 2) (i + 1) = (m + 2) * Nat.choose (m + 1) i := by
    simpa using choose_mul_eq (m + 1) i
  have h2 : (m + 1 - i) * Nat.choose (m + 1) i = (m + 1) * Nat.choose m i := by
    have hsym := choose_mul_eq m (m - i)
    have hmi : m - (m - i) = i := by omega
    have hm1i : m + 1 - (m - i + 1) = i := by omega
    have hsub : m - i + 1 = m + 1 - i := by omega
    rw [← Nat.choose_symm (by omega : m - i ≤ m), hmi,
      ← Nat.choose_symm (by omega : m - i + 1 ≤ m + 1), hm1i, hsub] at hsym
    exact hsym
  have h3 : (t + 1) * Nat.choose (i + 1) (t + 1) = (i + 1) * Nat.choose i t :=
    choose_mul_eq i t
  have h4 : (m + t + 1 - i - j) * Nat.choose (m + 1 - i) (j - t) =
      (m + 1 - i) * Nat.choose (m - i) (j - t) := by
    have hsym := choose_mul_eq (m - i) (m - i - (j - t))
    have ha : m - i - (j - t) ≤ m - i := Nat.sub_le _ _
    have hb : m - i - (m - i - (j - t)) = j - t := by omega
    have hc : m - i - (j - t) + 1 ≤ m + 1 - i := by omega
    have hd : m + 1 - i - (m - i - (j - t) + 1) = j - t := by omega
    have hadd : m - i + 1 = m + 1 - i := by omega
    have he : m - i - (j - t) + 1 = m + t + 1 - i - j := by omega
    rw [← Nat.choose_symm ha, hb, hadd, ← Nat.choose_symm hc, hd, he] at hsym
    exact hsym
  have hsub1 : m + 2 - (i + 1) = m + 1 - i := by omega
  have hsub2 : j + 1 - (t + 1) = j - t := by omega
  rw [hsub1, hsub2]
  have hpos1 : 0 < (i + 1) * (m + 1 - i) := Nat.mul_pos (Nat.succ_pos i) (by omega)
  apply Nat.eq_of_mul_eq_mul_left hpos1
  calc (i + 1) * (m + 1 - i) *
        ((t + 1) * (m + t + 1 - i - j) *
          (Nat.choose (m + 2) (i + 1) * Nat.choose (i + 1) (t + 1) * Nat.choose (m + 1 - i) (j - t)))
      = ((i + 1) * Nat.choose (m + 2) (i + 1)) * (m + 1 - i) *
          ((t + 1) * Nat.choose (i + 1) (t + 1)) *
          ((m + t + 1 - i - j) * Nat.choose (m + 1 - i) (j - t)) := by ring
    _ = ((m + 2) * Nat.choose (m + 1) i) * (m + 1 - i) *
          ((i + 1) * Nat.choose i t) * ((m + 1 - i) * Nat.choose (m - i) (j - t)) := by
          rw [h1, h3, h4]
    _ = (i + 1) * (m + 1 - i) * (m + 2) * ((m + 1 - i) * Nat.choose (m + 1) i) *
          Nat.choose i t * Nat.choose (m - i) (j - t) := by ring
    _ = (i + 1) * (m + 1 - i) * (m + 2) * ((m + 1) * Nat.choose m i) *
          Nat.choose i t * Nat.choose (m - i) (j - t) := by rw [h2]
    _ = (i + 1) * (m + 1 - i) *
          ((m + 2) * (m + 1) * (Nat.choose m i * Nat.choose i t * Nat.choose (m - i) (j - t))) := by ring

private lemma pairCount_shift_opp {m i j t : ℕ} (h : ValidTriple m i j t) :
    (i + 1 - t) * (j + 1 - t) * pairCount (m + 2) (i + 1) (j + 1) t =
      (m + 2) * (m + 1) * pairCount m i j t := by
  obtain ⟨hi, hj, hti, htj, hij⟩ := h
  unfold pairCount
  have h1 : (i + 1) * Nat.choose (m + 2) (i + 1) = (m + 2) * Nat.choose (m + 1) i := by
    simpa using choose_mul_eq (m + 1) i
  have h2 : (m + 1 - i) * Nat.choose (m + 1) i = (m + 1) * Nat.choose m i := by
    have hsym := choose_mul_eq m (m - i)
    have hmi : m - (m - i) = i := by omega
    have hm1i : m + 1 - (m - i + 1) = i := by omega
    have hsub : m - i + 1 = m + 1 - i := by omega
    rw [← Nat.choose_symm (by omega : m - i ≤ m), hmi,
      ← Nat.choose_symm (by omega : m - i + 1 ≤ m + 1), hm1i, hsub] at hsym
    exact hsym
  have h3 : (i + 1 - t) * Nat.choose (i + 1) t = (i + 1) * Nat.choose i t := by
    have hsym := choose_mul_eq i (i - t)
    have ha : i - t ≤ i := Nat.sub_le _ _
    have hb : i - (i - t) = t := by omega
    have hc : i - t + 1 ≤ i + 1 := by omega
    have hd : i + 1 - (i - t + 1) = t := by omega
    have he : i - t + 1 = i + 1 - t := by omega
    rw [← Nat.choose_symm ha, hb, ← Nat.choose_symm hc, hd, he] at hsym
    exact hsym
  have h4 : (j + 1 - t) * Nat.choose (m + 1 - i) (j + 1 - t) =
      (m + 1 - i) * Nat.choose (m - i) (j - t) := by
    have hsym := choose_mul_eq (m - i) (j - t)
    have hadd1 : m - i + 1 = m + 1 - i := by omega
    have hadd2 : j - t + 1 = j + 1 - t := by omega
    rw [hadd1, hadd2] at hsym
    exact hsym
  have hsub1 : m + 2 - (i + 1) = m + 1 - i := by omega
  rw [hsub1]
  have hpos1 : 0 < (i + 1) * (m + 1 - i) := Nat.mul_pos (Nat.succ_pos i) (by omega)
  apply Nat.eq_of_mul_eq_mul_left hpos1
  calc (i + 1) * (m + 1 - i) *
        ((i + 1 - t) * (j + 1 - t) *
          (Nat.choose (m + 2) (i + 1) * Nat.choose (i + 1) t * Nat.choose (m + 1 - i) (j + 1 - t)))
      = ((i + 1) * Nat.choose (m + 2) (i + 1)) * (m + 1 - i) *
          ((i + 1 - t) * Nat.choose (i + 1) t) *
          ((j + 1 - t) * Nat.choose (m + 1 - i) (j + 1 - t)) := by ring
    _ = ((m + 2) * Nat.choose (m + 1) i) * (m + 1 - i) *
          ((i + 1) * Nat.choose i t) * ((m + 1 - i) * Nat.choose (m - i) (j - t)) := by
          rw [h1, h3, h4]
    _ = (i + 1) * (m + 1 - i) * (m + 2) * ((m + 1 - i) * Nat.choose (m + 1) i) *
          Nat.choose i t * Nat.choose (m - i) (j - t) := by ring
    _ = (i + 1) * (m + 1 - i) * (m + 2) * ((m + 1) * Nat.choose m i) *
          Nat.choose i t * Nat.choose (m - i) (j - t) := by rw [h2]
    _ = (i + 1) * (m + 1 - i) *
          ((m + 2) * (m + 1) * (Nat.choose m i * Nat.choose i t * Nat.choose (m - i) (j - t))) := by ring

/-- Antisymmetrized 2-coordinate restriction `g_{u, v}(z) = g(z|_{u=1,v=0}) - g(z|_{u=0,v=1})`. -/
def antiSym {m : ℕ} (g : (Fin (m + 2) → Bool) → ℝ) (u : Fin (m + 2)) (v : Fin (m + 1)) :
    (Fin m → Bool) → ℝ :=
  fun z => g (insertTwo u v true false z) - g (insertTwo u v false true z)

/-- **Key Difference Identity**:
Summing `pairCorrR (antiSym g u v) i j t` over all `(u, v)` applies `2(m+2)(m+1) · Δ_t`! -/
private lemma sum_antiSym_pairCorrR {m i j t : ℕ} (g : (Fin (m + 2) → Bool) → ℝ)
    (h : ValidTriple m i j t) :
    ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), pairCorrR (antiSym g u v) i j t =
      2 * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) *
        (pairCorrR g (i + 1) (j + 1) (t + 1) - pairCorrR g (i + 1) (j + 1) t) := by
  have hpc0 : (pairCount m i j t : ℝ) ≠ 0 := by exact_mod_cast (pairCount_pos h).ne'
  have hvalid1 : ValidTriple (m + 2) (i + 1) (j + 1) (t + 1) := by
    obtain ⟨hi, hj, hti, htj, hij⟩ := h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hvalid2 : ValidTriple (m + 2) (i + 1) (j + 1) t := by
    obtain ⟨hi, hj, hti, htj, hij⟩ := h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hpc1 : (pairCount (m + 2) (i + 1) (j + 1) (t + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (pairCount_pos hvalid1).ne'
  have hpc2 : (pairCount (m + 2) (i + 1) (j + 1) t : ℝ) ≠ 0 := by
    exact_mod_cast (pairCount_pos hvalid2).ne'
  have hmul : (pairCount m i j t : ℝ) *
      ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), pairCorrR (antiSym g u v) i j t =
      ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
        antiSym g u v p.1 * antiSym g u v p.2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _
    unfold pairCorrR; field_simp [hpc0]
  have hexp : ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
        antiSym g u v p.1 * antiSym g u v p.2 =
      (∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
        g (insertTwo u v true false p.1) * g (insertTwo u v true false p.2)) +
      (∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
        g (insertTwo u v false true p.1) * g (insertTwo u v false true p.2)) -
      (∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
        g (insertTwo u v true false p.1) * g (insertTwo u v false true p.2)) -
      (∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ p ∈ pairSet m i j t,
        g (insertTwo u v false true p.1) * g (insertTwo u v true false p.2)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    apply Finset.sum_congr rfl; intro v _
    apply Finset.sum_congr rfl; intro p _
    unfold antiSym; ring
  have hs1 := sum_insertTwo_same (i := i) (j := j) (t := t) g true
  have hs2 := sum_insertTwo_same (i := i) (j := j) (t := t) g false
  have ho1 := sum_insertTwo_opp (i := i) (j := j) (t := t) g true
  have ho2 := sum_insertTwo_opp (i := i) (j := j) (t := t) g false
  simp only [Bool.not_true, Bool.not_false] at hs1 hs2 ho1 ho2
  have hsum1 : ∑ q ∈ pairSet (m + 2) (i + 1) (j + 1) (t + 1), g q.1 * g q.2 =
      (pairCount (m + 2) (i + 1) (j + 1) (t + 1) : ℝ) * pairCorrR g (i + 1) (j + 1) (t + 1) := by
    unfold pairCorrR; field_simp [hpc1]
  have hsum2 : ∑ q ∈ pairSet (m + 2) (i + 1) (j + 1) t, g q.1 * g q.2 =
      (pairCount (m + 2) (i + 1) (j + 1) t : ℝ) * pairCorrR g (i + 1) (j + 1) t := by
    unfold pairCorrR; field_simp [hpc2]
  have hsh1 : (((t + 1) * (m + t + 1 - i - j) : ℕ) : ℝ) *
      (pairCount (m + 2) (i + 1) (j + 1) (t + 1) : ℝ) =
      ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * (pairCount m i j t : ℝ) := by
    have := pairCount_shift_same h
    exact_mod_cast this
  have hsh2 : (((i + 1 - t) * (j + 1 - t) : ℕ) : ℝ) *
      (pairCount (m + 2) (i + 1) (j + 1) t : ℝ) =
      ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * (pairCount m i j t : ℝ) := by
    have := pairCount_shift_opp h
    exact_mod_cast this
  apply mul_left_cancel₀ hpc0
  rw [hmul, hexp, hs1, hs2, ho1, ho2, hsum1, hsum2]
  linear_combination 2 * pairCorrR g (i + 1) (j + 1) (t + 1) * hsh1 -
    2 * pairCorrR g (i + 1) (j + 1) t * hsh2

/-- Pascal-identity finite-difference step on `k`. -/
private lemma finDiff_step_real (k : ℕ) (h : ℕ → ℝ) :
    ∑ a ∈ Finset.range (k + 1),
      (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) * (h (a + 1) - h a) =
    ∑ a ∈ Finset.range (k + 2),
      (((-1 : ℤ) ^ (k + 1 - a) * (Nat.choose (k + 1) a : ℤ) : ℤ) : ℝ) * h a := by
  have hsplit : ∑ a ∈ Finset.range (k + 1),
      (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) * (h (a + 1) - h a) =
      (∑ a ∈ Finset.range (k + 1),
        (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) * h (a + 1)) -
      (∑ a ∈ Finset.range (k + 1),
        (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) * h a) := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro a _; ring
  rw [hsplit]
  rw [Finset.sum_range_succ' (fun a => (((-1 : ℤ) ^ (k + 1 - a) * (Nat.choose (k + 1) a : ℤ) : ℤ) : ℝ) * h a)]
  rw [Finset.sum_range_succ' (fun a => (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) * h a)]
  have hlast : ∑ a ∈ Finset.range (k + 1),
      (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) * h (a + 1) =
      (∑ a ∈ Finset.range k,
        (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) * h (a + 1)) +
      h (k + 1) := by
    rw [Finset.sum_range_succ]; simp
  rw [hlast]
  have hlastR : ∑ a ∈ Finset.range (k + 1),
      (((-1 : ℤ) ^ (k + 1 - (a + 1)) * (Nat.choose (k + 1) (a + 1) : ℤ) : ℤ) : ℝ) * h (a + 1) =
      (∑ a ∈ Finset.range k,
        (((-1 : ℤ) ^ (k - a) * (Nat.choose (k + 1) (a + 1) : ℤ) : ℤ) : ℝ) * h (a + 1)) +
      h (k + 1) := by
    rw [Finset.sum_range_succ]; simp
  rw [hlastR]
  have hmid :
      (∑ a ∈ Finset.range k,
        (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) * h (a + 1)) -
      (∑ a ∈ Finset.range k,
        (((-1 : ℤ) ^ (k - (a + 1)) * (Nat.choose k (a + 1) : ℤ) : ℤ) : ℝ) * h (a + 1)) =
      ∑ a ∈ Finset.range k,
        (((-1 : ℤ) ^ (k - a) * (Nat.choose (k + 1) (a + 1) : ℤ) : ℤ) : ℝ) * h (a + 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro a ha
    have hak : a < k := Finset.mem_range.mp ha
    have hexp : k - a = (k - (a + 1)) + 1 := by omega
    rw [Nat.choose_succ_succ, hexp, pow_succ]
    push_cast; ring
  have h0 : (((-1 : ℤ) ^ (k + 1 - 0) * (Nat.choose (k + 1) 0 : ℤ) : ℤ) : ℝ) * h 0 =
      -(((((-1 : ℤ) ^ (k - 0) * (Nat.choose k 0 : ℤ) : ℤ) : ℝ)) * h 0) := by
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_succ]
    push_cast; ring
  rw [h0]; linarith

/-- **Universal Terwilliger PSD Nonnegativity Theorem**:
For every `k, n : ℕ` with `2 * k ≤ n`, every real function `g : (Fin n → Bool) → ℝ`, and every
weight function `w : ℕ → ℝ`, the quadratic form `w^T B̃^(k) w` is nonnegative. -/
theorem terwilliger_psd_nonneg_real :
    ∀ (k n : ℕ), 2 * k ≤ n → ∀ (g : (Fin n → Bool) → ℝ) (w : ℕ → ℝ),
      0 ≤ ∑ r ∈ Finset.range (n - 2 * k + 1), ∑ c ∈ Finset.range (n - 2 * k + 1),
        w r * w c * bTilde k g r c
  | 0, n, _, g, w => by
    have hb0 : ∀ r ∈ Finset.range (n + 1), ∀ c ∈ Finset.range (n + 1),
        bTilde 0 g r c = realLayerSum g r * realLayerSum g c := by
      intro r hr c hc
      have hrn : r ≤ n := by rw [Finset.mem_range] at hr; omega
      have hcn : c ≤ n := by rw [Finset.mem_range] at hc; omega
      unfold bTilde
      simp only [Nat.mul_zero, Nat.sub_zero, Finset.range_one, Finset.sum_singleton,
        Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, Int.cast_one, one_mul, zero_add]
      have hterm : ∀ b ∈ Finset.Icc (r + c - n) (min r c),
          (pairCount n r c b : ℝ) * pairCorrR g r c b =
            ∑ p ∈ pairSet n r c b, g p.1 * g p.2 := by
        intro b hb
        obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
        have hvalid : ValidTriple n r c b :=
          ⟨hrn, hcn, hb2.trans (min_le_left r c), hb2.trans (min_le_right r c), by omega⟩
        have hpc : (pairCount n r c b : ℝ) ≠ 0 := by exact_mod_cast (pairCount_pos hvalid).ne'
        unfold pairCorrR; field_simp [hpc]
      rw [Finset.sum_congr rfl hterm]
      have hmaps : ∀ p ∈ hammingLayer n r ×ˢ hammingLayer n c,
          (supportOf p.1 ∩ supportOf p.2).card ∈ Finset.Icc (r + c - n) (min r c) := by
        intro p hp
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
        have hxr : (supportOf p.1).card = r := (Finset.mem_filter.mp hx).2
        have hyc : (supportOf p.2).card = c := (Finset.mem_filter.mp hy).2
        rw [Finset.mem_Icc]
        refine ⟨?_, le_min ?_ ?_⟩
        · have hu : (supportOf p.1 ∪ supportOf p.2).card ≤ n := by
            simpa using Finset.card_le_univ (supportOf p.1 ∪ supportOf p.2)
          have hinc := Finset.card_union_add_card_inter (supportOf p.1) (supportOf p.2)
          omega
        · rw [← hxr]; exact Finset.card_le_card Finset.inter_subset_left
        · rw [← hyc]; exact Finset.card_le_card Finset.inter_subset_right
      simp only [pairSet]
      rw [Finset.sum_fiberwise_of_maps_to hmaps, realLayerSum, realLayerSum, Finset.sum_product,
        Finset.sum_mul]
      apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum]
    have hsq : ∑ r ∈ Finset.range (n - 2 * 0 + 1), ∑ c ∈ Finset.range (n - 2 * 0 + 1),
          w r * w c * bTilde 0 g r c =
        (∑ r ∈ Finset.range (n + 1), w r * realLayerSum g r) ^ 2 := by
      simp only [Nat.mul_zero, Nat.sub_zero]
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro r hr
      apply Finset.sum_congr rfl; intro c hc
      rw [hb0 r hr c hc]; ring
    rw [hsq]; exact sq_nonneg _
  | k + 1, n, hkn, g, w => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hkm : 2 * k ≤ m := by omega
    have hsub_eq : m + 2 - 2 * (k + 1) = m - 2 * k := by omega
    -- Apply IH to `antiSym g u v` for all `(u, v)` and sum!
    have hsum_nn : 0 ≤ ∑ u : Fin (m + 2), ∑ v : Fin (m + 1),
        ∑ r ∈ Finset.range (m - 2 * k + 1), ∑ c ∈ Finset.range (m - 2 * k + 1),
          w r * w c * bTilde k (antiSym g u v) r c := by
      apply Finset.sum_nonneg; intro u _
      apply Finset.sum_nonneg; intro v _
      exact terwilliger_psd_nonneg_real k m hkm (antiSym g u v) w
    -- Key identity: summing `bTilde k (antiSym g u v) r c` over `(u, v)` equals `2(m+2)(m+1) * bTilde (k+1) g r c`!
    have hstep_b : ∀ r ∈ Finset.range (m - 2 * k + 1), ∀ c ∈ Finset.range (m - 2 * k + 1),
        ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), bTilde k (antiSym g u v) r c =
          2 * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * bTilde (k + 1) g r c := by
      intro r hr c hc
      have hrm : r ≤ m - 2 * k := by rw [Finset.mem_range] at hr; omega
      have hcm : c ≤ m - 2 * k := by rw [Finset.mem_range] at hc; omega
      unfold bTilde
      rw [hsub_eq, Finset.mul_sum]
      calc ∑ u : Fin (m + 2), ∑ v : Fin (m + 1),
            ∑ b ∈ Finset.Icc (r + c - (m - 2 * k)) (min r c),
              (pairCount (m - 2 * k) r c b : ℝ) *
                ∑ a ∈ Finset.range (k + 1),
                  (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                    pairCorrR (antiSym g u v) (k + r) (k + c) (a + b)
          = ∑ b ∈ Finset.Icc (r + c - (m - 2 * k)) (min r c),
              (pairCount (m - 2 * k) r c b : ℝ) *
                ∑ a ∈ Finset.range (k + 1),
                  (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                    (∑ u : Fin (m + 2), ∑ v : Fin (m + 1),
                      pairCorrR (antiSym g u v) (k + r) (k + c) (a + b)) := by
            trans ∑ u : Fin (m + 2), ∑ b ∈ Finset.Icc (r + c - (m - 2 * k)) (min r c),
                ∑ v : Fin (m + 1),
                  (pairCount (m - 2 * k) r c b : ℝ) *
                    ∑ a ∈ Finset.range (k + 1),
                      (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                        pairCorrR (antiSym g u v) (k + r) (k + c) (a + b)
            · apply Finset.sum_congr rfl; intro u _; exact Finset.sum_comm
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro b _
              simp_rw [← Finset.mul_sum]; congr 1
              trans ∑ a ∈ Finset.range (k + 1), ∑ u : Fin (m + 2), ∑ v : Fin (m + 1),
                  (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                    pairCorrR (antiSym g u v) (k + r) (k + c) (a + b)
              · calc ∑ u : Fin (m + 2), ∑ v : Fin (m + 1), ∑ a ∈ Finset.range (k + 1),
                      (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                        pairCorrR (antiSym g u v) (k + r) (k + c) (a + b)
                    = ∑ u : Fin (m + 2), ∑ a ∈ Finset.range (k + 1), ∑ v : Fin (m + 1),
                        (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                          pairCorrR (antiSym g u v) (k + r) (k + c) (a + b) :=
                      Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
                  _ = _ := Finset.sum_comm
              · apply Finset.sum_congr rfl; intro a _
                simp_rw [← Finset.mul_sum]
        _ = ∑ b ∈ Finset.Icc (r + c - (m - 2 * k)) (min r c),
              2 * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) *
                ((pairCount (m - 2 * k) r c b : ℝ) *
                  ∑ a ∈ Finset.range (k + 2),
                    (((-1 : ℤ) ^ (k + 1 - a) * (Nat.choose (k + 1) a : ℤ) : ℤ) : ℝ) *
                      pairCorrR g (k + 1 + r) (k + 1 + c) (a + b)) := by
            apply Finset.sum_congr rfl; intro b hb
            obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
            have hbr : b ≤ r := hb2.trans (min_le_left r c)
            have hbc : b ≤ c := hb2.trans (min_le_right r c)
            have hinner : ∀ a ∈ Finset.range (k + 1),
                ∑ u : Fin (m + 2), ∑ v : Fin (m + 1),
                  pairCorrR (antiSym g u v) (k + r) (k + c) (a + b) =
                2 * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) *
                  (pairCorrR g (k + 1 + r) (k + 1 + c) (a + 1 + b) -
                   pairCorrR g (k + 1 + r) (k + 1 + c) (a + b)) := by
              intro a ha
              have hak : a ≤ k := by rw [Finset.mem_range] at ha; omega
              have hval : ValidTriple m (k + r) (k + c) (a + b) :=
                ⟨by omega, by omega, by omega, by omega, by omega⟩
              have hres := sum_antiSym_pairCorrR g hval
              have h1 : k + r + 1 = k + 1 + r := by omega
              have h2 : k + c + 1 = k + 1 + c := by omega
              have h3 : a + b + 1 = a + 1 + b := by omega
              rwa [h1, h2, h3] at hres
            calc (pairCount (m - 2 * k) r c b : ℝ) *
                  ∑ a ∈ Finset.range (k + 1),
                    (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                      (∑ u : Fin (m + 2), ∑ v : Fin (m + 1),
                        pairCorrR (antiSym g u v) (k + r) (k + c) (a + b))
                = (pairCount (m - 2 * k) r c b : ℝ) *
                    (2 * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) *
                      ∑ a ∈ Finset.range (k + 1),
                        (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                          (pairCorrR g (k + 1 + r) (k + 1 + c) (a + 1 + b) -
                           pairCorrR g (k + 1 + r) (k + 1 + c) (a + b))) := by
                  congr 1
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl; intro a ha
                  rw [hinner a ha]; ring
              _ = _ := by
                  rw [finDiff_step_real k (fun a => pairCorrR g (k + 1 + r) (k + 1 + c) (a + b))]
                  ring
    have hfactor : ∑ u : Fin (m + 2), ∑ v : Fin (m + 1),
          ∑ r ∈ Finset.range (m - 2 * k + 1), ∑ c ∈ Finset.range (m - 2 * k + 1),
            w r * w c * bTilde k (antiSym g u v) r c =
        2 * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) *
          ∑ r ∈ Finset.range (m + 2 - 2 * (k + 1) + 1), ∑ c ∈ Finset.range (m + 2 - 2 * (k + 1) + 1),
            w r * w c * bTilde (k + 1) g r c := by
      rw [hsub_eq, Finset.mul_sum]
      calc ∑ u : Fin (m + 2), ∑ v : Fin (m + 1),
            ∑ r ∈ Finset.range (m - 2 * k + 1), ∑ c ∈ Finset.range (m - 2 * k + 1),
              w r * w c * bTilde k (antiSym g u v) r c
          = ∑ r ∈ Finset.range (m - 2 * k + 1), ∑ c ∈ Finset.range (m - 2 * k + 1),
              w r * w c * (∑ u : Fin (m + 2), ∑ v : Fin (m + 1), bTilde k (antiSym g u v) r c) := by
            trans ∑ u : Fin (m + 2), ∑ r ∈ Finset.range (m - 2 * k + 1),
                ∑ v : Fin (m + 1), ∑ c ∈ Finset.range (m - 2 * k + 1),
                  w r * w c * bTilde k (antiSym g u v) r c
            · exact Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro r _
              trans ∑ u : Fin (m + 2), ∑ c ∈ Finset.range (m - 2 * k + 1), ∑ v : Fin (m + 1),
                  w r * w c * bTilde k (antiSym g u v) r c
              · exact Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
              · rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro c _
                simp_rw [← Finset.mul_sum]
        _ = ∑ r ∈ Finset.range (m - 2 * k + 1),
              2 * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) *
                ∑ c ∈ Finset.range (m - 2 * k + 1), w r * w c * bTilde (k + 1) g r c := by
            apply Finset.sum_congr rfl; intro r hr
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro c hc
            rw [hstep_b r hr c hc]; ring
    rw [hfactor] at hsum_nn
    have hpos : (0 : ℝ) < 2 * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by positivity
    nlinarith

/-- List-sum form of `terwilliger_psd_nonneg_real`: works directly with sparse `w : List (ℕ × ℤ)`
(even without duplicate checks!). -/
noncomputable def evalPsdList {n : ℕ} (k : ℕ) (f : BooleanFun n) (w : List (ℕ × ℤ)) : ℝ :=
  (w.map (fun p =>
    (w.map (fun q =>
      (p.2 : ℝ) * (q.2 : ℝ) * bTilde k (fun x => boolToReal (f x)) p.1 q.1)).sum)).sum

theorem evalPsdList_nonneg {n k : ℕ} (hkn : 2 * k ≤ n) (f : BooleanFun n)
    (w : List (ℕ × ℤ)) (hw : ∀ p ∈ w, p.1 ≤ n - 2 * k) :
    0 ≤ evalPsdList k f w := by
  let wf : ℕ → ℝ := fun r => ((w.filter (fun p => p.1 == r)).map (fun p => (p.2 : ℝ))).sum
  have hmain := terwilliger_psd_nonneg_real k n hkn (fun x => boolToReal (f x)) wf
  have hwf_eq : ∀ (h : ℕ → ℝ),
      (w.map (fun p => (p.2 : ℝ) * h p.1)).sum =
        ∑ r ∈ Finset.range (n - 2 * k + 1), wf r * h r := by
    intro h
    clear hmain
    induction w with
    | nil => simp [wf]
    | cons hd tl ih =>
      have hhd : hd.1 ≤ n - 2 * k := hw hd (List.mem_cons_self ..)
      have htl : ∀ p ∈ tl, p.1 ≤ n - 2 * k := fun p hp => hw p (List.mem_cons_of_mem _ hp)
      simp only [List.map_cons, List.sum_cons]
      rw [ih htl]
      have hwf_cons : ∀ r, ((List.filter (fun p => p.1 == r) (hd :: tl)).map (fun p => (p.2 : ℝ))).sum =
          (if hd.1 = r then (hd.2 : ℝ) else 0) +
            ((List.filter (fun p => p.1 == r) tl).map (fun p => (p.2 : ℝ))).sum := by
        intro r
        by_cases hr : hd.1 = r
        · subst hr; simp
        · have hbeq : (hd.1 == r) = false := by simp [hr]
          simp [hbeq, hr]
      calc (hd.2 : ℝ) * h hd.1 +
            ∑ r ∈ Finset.range (n - 2 * k + 1),
              ((List.filter (fun p => p.1 == r) tl).map (fun p => (p.2 : ℝ))).sum * h r
          = (∑ r ∈ Finset.range (n - 2 * k + 1), (if hd.1 = r then (hd.2 : ℝ) else 0) * h r) +
            ∑ r ∈ Finset.range (n - 2 * k + 1),
              ((List.filter (fun p => p.1 == r) tl).map (fun p => (p.2 : ℝ))).sum * h r := by
            congr 1
            rw [Finset.sum_eq_single hd.1]
            · simp
            · intro b _ hne; simp [hne.symm]
            · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
        _ = ∑ r ∈ Finset.range (n - 2 * k + 1),
              ((List.filter (fun p => p.1 == r) (hd :: tl)).map (fun p => (p.2 : ℝ))).sum * h r := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro r _
            rw [hwf_cons r]; ring
  have heq : evalPsdList k f w =
      ∑ r ∈ Finset.range (n - 2 * k + 1), ∑ c ∈ Finset.range (n - 2 * k + 1),
        wf r * wf c * bTilde k (fun x => boolToReal (f x)) r c := by
    unfold evalPsdList
    have hinner : ∀ p : ℕ × ℤ,
        (w.map (fun q => (p.2 : ℝ) * (q.2 : ℝ) * bTilde k (fun x => boolToReal (f x)) p.1 q.1)).sum =
          (p.2 : ℝ) * ∑ c ∈ Finset.range (n - 2 * k + 1),
            wf c * bTilde k (fun x => boolToReal (f x)) p.1 c := by
      intro p
      rw [← hwf_eq (fun c => bTilde k (fun x => boolToReal (f x)) p.1 c)]
      have hpull : ∀ l : List (ℕ × ℤ),
          (l.map (fun q => (p.2 : ℝ) * (q.2 : ℝ) * bTilde k (fun x => boolToReal (f x)) p.1 q.1)).sum =
            (p.2 : ℝ) * (l.map (fun q => (q.2 : ℝ) * bTilde k (fun x => boolToReal (f x)) p.1 q.1)).sum := by
        intro l; induction l with
        | nil => simp
        | cons a tl ihl => simp [ihl]; ring
      exact hpull w
    have h1 : (w.map (fun p =>
          (w.map (fun q => (p.2 : ℝ) * (q.2 : ℝ) * bTilde k (fun x => boolToReal (f x)) p.1 q.1)).sum)).sum =
        (w.map (fun p => (p.2 : ℝ) *
          ∑ c ∈ Finset.range (n - 2 * k + 1), wf c * bTilde k (fun x => boolToReal (f x)) p.1 c)).sum := by
      congr 1; apply List.map_congr_left; intro p _; exact hinner p
    rw [h1, hwf_eq (fun r => ∑ c ∈ Finset.range (n - 2 * k + 1), wf c * bTilde k (fun x => boolToReal (f x)) r c)]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _; ring
  rw [heq]; exact hmain

/-! ### Part 2: 2-Stage `mTrie → cTrie` Binomial-Basis + PSD Verifier -/

/-- Pure-integer Step-3 certificate step in the bivariate binomial basis `c_{j, r, s}`
with fixed integer layer sums `S : ℕ → ℕ` and sparse Terwilliger PSD cuts `ubPsd`. -/
inductive PsdBinoStep where
  | eqSym (i j t : ℕ) (μ : ℤ)
  | eqDiag (i : ℕ) (μ : ℤ)
  | eqHyp (i j : ℕ) (μ : ℤ)
  | ubMLo0 (i j t : ℕ) (lam : ℕ)
  | ubMMcc (i j t : ℕ) (lam : ℕ)
  | ubMLePi (i j t : ℕ) (lam : ℕ)
  | ubMLePj (i j t : ℕ) (lam : ℕ)
  | ubPsd (k : ℕ) (w : List (ℕ × ℤ)) (lam : ℕ)
  deriving Repr, DecidableEq

/-- Scale every stored leaf in an `IntTrie` by `c : ℤ` (keeps big-int multiplication outside inner loops). -/
def scaleTrie (c : ℤ) : IntTrie → IntTrie
  | .empty => .empty
  | .leaf v => .leaf (c * v)
  | .node lo hi => .node (scaleTrie c lo) (scaleTrie c hi)

private lemma wellFormed_and_eval_scaleTrie (val : ℕ → ℝ) (d : ℕ) (c : ℤ) :
    ∀ step base t,
      IntTrie.WellFormed d t →
      IntTrie.WellFormed d (scaleTrie c t) ∧
        IntTrie.evalTrie val step base (scaleTrie c t) = (c : ℝ) * IntTrie.evalTrie val step base t := by
  induction d with
  | zero =>
    intro step base t hwf
    cases t with
    | empty => simp [scaleTrie, IntTrie.evalTrie, hwf]
    | leaf v =>
      refine ⟨trivial, ?_⟩
      simp only [scaleTrie, IntTrie.evalTrie]; push_cast; ring
    | node _ _ => exact False.elim hwf
  | succ d ih =>
    intro step base t hwf
    cases t with
    | empty => simp [scaleTrie, IntTrie.evalTrie, IntTrie.wellFormed_empty]
    | leaf _ => exact False.elim hwf
    | node lo hi =>
      obtain ⟨hlo, hhi⟩ := hwf
      obtain ⟨hwfL, hevL⟩ := ih (2 * step) base lo hlo
      obtain ⟨hwfR, hevR⟩ := ih (2 * step) (base + step) hi hhi
      refine ⟨⟨hwfL, hwfR⟩, ?_⟩
      simp only [scaleTrie, IntTrie.evalTrie, hevL, hevR]; ring

/-- Inner `a`-loop updating a compact depth-5 `t`-trie with
`scaleB * ∑_{a=0}^k (-1)^(k-a) C(k, a) m(k+r, k+c, a+b)`. -/
def psdALoop5 (k b : ℕ) (scaleB : ℤ) : ℕ → ℕ → ℕ → IntTrie → IntTrie
  | 0, _, _, tr => tr
  | rem + 1, a, curA, tr =>
      let coef := scaleB * (altSign (k - a) * (curA : ℤ))
      let tr' := IntTrie.addAt 5 (a + b) coef tr
      psdALoop5 k b scaleB rem (a + 1) (curA * (k - a) / (a + 1)) tr'

/-- Middle `b`-loop updating a compact depth-5 `t`-trie for fixed `(r, c)` (`r ≤ c`),
computing `fastChoose (n - 2k) r` ONCE per `(r, c)` and `fastChoose r b * fastChoose (n-2k-r) (c-b)`
ONCE per `b` (zero `IntTrie.merge`, 10× fewer `fastChoose` calls!). -/
def psdBLoop5 (n2k k r c bLo : ℕ) (scaleRC_cN2kR : ℤ) : ℕ → ℕ → IntTrie → IntTrie
  | 0, _, tr => tr
  | rem + 1, off, tr =>
      let b := bLo + off
      let multB : ℤ := ((fastChoose r b * fastChoose (n2k - r) (c - b) : ℕ) : ℤ)
      let tr' := psdALoop5 k b (scaleRC_cN2kR * multB) (k + 1) 0 1 tr
      psdBLoop5 n2k k r c bLo scaleRC_cN2kR rem (off + 1) tr'

/-- Build `scaleRC * bTilde k f r c` as a depth-15 `IntTrie` via a single `modifyAt 10`
placement of a depth-5 `t`-trie. -/
def psdPairTrie (n k r c : ℕ) (scaleRC : ℤ) : IntTrie :=
  if scaleRC == 0 then .empty
  else
    let r' := min r c
    let c' := max r c
    let n2k := n - 2 * k
    let bLo := r' + c' - n2k
    let bHi := min r' c'
    let scaleRC_cN2kR := scaleRC * (fastChoose n2k r' : ℤ)
    IntTrie.modifyAt 10 ((k + r') + 32 * (k + c'))
      (psdBLoop5 n2k k r' c' bLo scaleRC_cN2kR (bHi - bLo + 1) 0) .empty

/-- Upper-triangular off-diagonal merge `∑_{(c, wc) ∈ tl} (2 * wr * wc) * bTilde k f r c`. -/
def psdUpperInner (n k r : ℕ) (wr : ℤ) : List (ℕ × ℤ) → IntTrie
  | [] => .empty
  | (c, wc) :: tl =>
      IntTrie.merge (psdPairTrie n k r c (2 * wr * wc)) (psdUpperInner n k r wr tl)

/-- Build unscaled `w^T B̃^(k) w` using upper-triangular symmetry `bTilde k f r c = bTilde k f c r`
(cuts `(r, c)` pairs in half!). -/
def psdUpperTrie (n k : ℕ) : List (ℕ × ℤ) → IntTrie
  | [] => .empty
  | (r, wr) :: tl =>
      IntTrie.merge
        (IntTrie.merge (psdPairTrie n k r r (wr * wr)) (psdUpperInner n k r wr tl))
        (psdUpperTrie n k tl)

/-- Side-condition check for `PsdBinoStep`. -/
def psdStepOk (n : ℕ) : PsdBinoStep → Bool
  | .eqSym i j t _ => validTripleB n i j t
  | .eqDiag i _ => decide (i ≤ n)
  | .eqHyp i j _ => decide (i ≤ n) && decide (j ≤ n)
  | .ubMLo0 i j t _ => validTripleB n i j t
  | .ubMMcc i j t _ => validTripleB n i j t
  | .ubMLePi i j t _ => validTripleB n i j t
  | .ubMLePj i j t _ => validTripleB n i j t
  | .ubPsd k w _ => decide (2 * k ≤ n) && w.all (fun p => decide (p.1 ≤ n - 2 * k))

/-- Direct `cTrie` contribution of `PsdBinoStep` (only `eqSym` touches `cTrie` directly!). -/
def psdStepC (n d : ℕ) : PsdBinoStep → IntTrie
  | .eqSym i j t μ => addEvalH n d i t (j - t) (-μ) (addEvalH n d j t (i - t) μ .empty)
  | _ => .empty

/-- Direct `mTrie` contribution of `PsdBinoStep` (aggregated before expanding to `cTrie`!). -/
def psdStepM (n : ℕ) : PsdBinoStep → IntTrie
  | .eqSym _ _ _ _ => .empty
  | .eqDiag i μ => IntTrie.addAt 15 (canonMKey i i i) (μ * (fastChoose n i : ℤ)) .empty
  | .eqHyp i j μ =>
      let tLo := i + j - n
      let tHi := min i j
      addHypLoop n i j tLo (μ * (fastChoose n i : ℤ)) (tHi - tLo + 1) 0 .empty
  | .ubMLo0 i j t lam => IntTrie.addAt 15 (canonMKey i j t) (lam : ℤ) .empty
  | .ubMMcc i j t lam =>
      let cni : ℤ := (fastChoose n i : ℤ)
      let cnj : ℤ := (fastChoose n j : ℤ)
      IntTrie.addAt 15 (canonMKey i j t) ((lam : ℤ) * (cni * cnj)) .empty
  | .ubMLePi i j t lam =>
      IntTrie.addAt 15 (canonMKey i j t) (-(lam : ℤ) * (fastChoose n i : ℤ)) .empty
  | .ubMLePj i j t lam =>
      IntTrie.addAt 15 (canonMKey i j t) (-(lam : ℤ) * (fastChoose n j : ℤ)) .empty
  | .ubPsd k w lam => scaleTrie (lam : ℤ) (psdUpperTrie n k w)

/-- Dual-objective contribution of `PsdBinoStep` given layer-sum lookup `S : ℕ → ℕ`. -/
def psdStepObj (n : ℕ) (S : ℕ → ℕ) : PsdBinoStep → ℤ
  | .eqSym _ _ _ _ => 0
  | .eqDiag i μ => μ * (S i : ℤ)
  | .eqHyp i j μ => μ * ((S i * S j : ℕ) : ℤ)
  | .ubMLo0 _ _ _ _ => 0
  | .ubMMcc i j _ lam =>
      let cni : ℤ := (fastChoose n i : ℤ)
      let cnj : ℤ := (fastChoose n j : ℤ)
      (lam : ℤ) * ((S i : ℤ) * cnj + (S j : ℤ) * cni - cni * cnj)
  | .ubMLePi i _ _ lam => -(lam : ℤ) * (S i : ℤ)
  | .ubMLePj _ j _ lam => -(lam : ℤ) * (S j : ℤ)
  | .ubPsd _ _ _ => 0

/-- Stage-2 expansion of a depth-15 `mTrie` into a depth-14 `cTrie`, validating each nonzero leaf! -/
def expandMTrieAux (n d : ℕ) : ℕ → ℕ → IntTrie → Bool × IntTrie
  | _, _, .empty => (true, .empty)
  | _, base, .leaf v =>
      if v == 0 then (true, .empty)
      else
        let i := base % 32
        let j := (base / 32) % 32
        let t := base / 1024
        if decide (i ≤ j) && validTripleB n i j t then
          (true, addEvalH n d j t (i - t) v .empty)
        else (false, .empty)
  | step, base, .node lo hi =>
      let (ok1, c1) := expandMTrieAux n d (2 * step) base lo
      let (ok2, c2) := expandMTrieAux n d (2 * step) (base + step) hi
      (ok1 && ok2, IntTrie.merge c1 c2)

/-- Pure-integer Farkas infeasibility checker for Step 3 (fixed layer sums + PSD cuts). -/
def checkPsdBinoFarkas (n d : ℕ) (S : ℕ → ℕ) (tree : BinTree PsdBinoStep) : Bool :=
  if decide (n < 32) && decide (d < 16) then
    let mAll := IntTrie.mergeTree (psdStepM n) tree
    let (mOk, cFromM) := expandMTrieAux n d 1 0 mAll
    let cAll := IntTrie.merge (IntTrie.mergeTree (psdStepC n d) tree) cFromM
    tree.all (psdStepOk n) && mOk && cAll.isZero && decide (0 < tree.sumZ (psdStepObj n S))
  else false

/-- Pure-integer LP bound checker for Step 3 proving
`(expectedLb : ℝ) ≤ (scale : ℝ) * evalTargetM f targetM`. -/
def checkPsdBinoBound (n d : ℕ) (S : ℕ → ℕ) (tree : BinTree PsdBinoStep)
    (targetM : List (ℕ × ℕ × ℕ × ℤ)) (scale : ℕ) (expectedLb : ℤ) : Bool :=
  if decide (n < 32) && decide (d < 16) && targetM.all (fun q => validTripleB n q.1 q.2.1 q.2.2.1) then
    let mRaw := IntTrie.mergeTree (psdStepM n) tree
    let mSub := addMList (-(scale : ℤ)) targetM mRaw
    let (mOk, cFromM) := expandMTrieAux n d 1 0 mSub
    let cAll := IntTrie.merge (IntTrie.mergeTree (psdStepC n d) tree) cFromM
    tree.all (psdStepOk n) && mOk && cAll.isZero && decide (expectedLb ≤ tree.sumZ (psdStepObj n S))
  else false

/-! #### Soundness of the 2-Stage `PsdBino` Verifier -/

private lemma bTilde_comm {n : ℕ} (f : BooleanFun n) (k r c : ℕ)
    (hkn : 2 * k ≤ n) (hr : r ≤ n - 2 * k) (hc : c ≤ n - 2 * k) :
    bTilde k (fun x => boolToReal (f x)) r c = bTilde k (fun x => boolToReal (f x)) c r := by
  unfold bTilde
  have hIcc : Finset.Icc (r + c - (n - 2 * k)) (min r c) =
      Finset.Icc (c + r - (n - 2 * k)) (min c r) := by
    rw [add_comm r c, min_comm r c]
  rw [hIcc]
  apply Finset.sum_congr rfl; intro b hb
  obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
  have hbr : b ≤ r := hb2.trans (min_le_right c r)
  have hbc : b ≤ c := hb2.trans (min_le_left c r)
  have hval_b : ValidTriple (n - 2 * k) r c b := ⟨hr, hc, hbr, hbc, by omega⟩
  rw [pairCount_symm hval_b]
  congr 1
  apply Finset.sum_congr rfl; intro a ha
  have hak : a ≤ k := by rw [Finset.mem_range] at ha; omega
  have hval_a : ValidTriple n (k + r) (k + c) (a + b) :=
    ⟨by omega, by omega, by omega, by omega, by omega⟩
  simp only [pairCorrR_bool]
  rw [pairCorr_symm f hval_a]

private lemma wellFormed_and_eval_psdALoop5 {n : ℕ} (f : BooleanFun n)
    (val : ℕ → ℝ) (step base : ℕ)
    (hn : n < 32) (k r c b : ℕ) (scaleB : ℤ)
    (hkr : k + r ≤ n) (hkc : k + c ≤ n) (hbr : b ≤ r) (hbc : b ≤ c)
    (hb_lo : r + c - (n - 2 * k) ≤ b) (hkn : 2 * k ≤ n)
    (hval : ∀ t, ValidTriple n (k + r) (k + c) t →
      val (base + step * t) = pairCorr f (k + r) (k + c) t) :
    ∀ rem a curA tr,
      a + rem ≤ k + 1 → curA = Nat.choose k a → IntTrie.WellFormed 5 tr →
      IntTrie.WellFormed 5 (psdALoop5 k b scaleB rem a curA tr) ∧
        IntTrie.evalTrie val step base
            (psdALoop5 k b scaleB rem a curA tr) =
          IntTrie.evalTrie val step base tr +
            (scaleB : ℝ) *
              ∑ m ∈ Finset.range rem,
                (((-1 : ℤ) ^ (k - (a + m)) * (Nat.choose k (a + m) : ℤ) : ℤ) : ℝ) *
                  pairCorr f (k + r) (k + c) ((a + m) + b)
  | 0, _, _, tr, _, _, hwf => by simp [psdALoop5, hwf]
  | rem + 1, a, curA, tr, hlt, hcur, hwf => by
    simp only [psdALoop5]
    have hab32 : a + b < 2 ^ 5 := by omega
    have hvalid : ValidTriple n (k + r) (k + c) (a + b) :=
      ⟨hkr, hkc, by omega, by omega, by omega⟩
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_addAt val 5 (a + b) step base
      (scaleB * (altSign (k - a) * (curA : ℤ))) tr hab32 hwf
    have hnext : curA * (k - a) / (a + 1) = Nat.choose k (a + 1) := by
      rw [hcur]; exact choose_step_div k a
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_psdALoop5 f val step base hn k r c b scaleB
      hkr hkc hbr hbc hb_lo hkn hval rem (a + 1) (curA * (k - a) / (a + 1)) _ (by omega) hnext hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1, Finset.sum_range_succ', hcur, altSign_eq]
    have hshift :
        ∑ m ∈ Finset.range rem,
          (((-1 : ℤ) ^ (k - (a + 1 + m)) * (Nat.choose k (a + 1 + m) : ℤ) : ℤ) : ℝ) *
            pairCorr f (k + r) (k + c) (a + 1 + m + b) =
        ∑ m ∈ Finset.range rem,
          (((-1 : ℤ) ^ (k - (a + (m + 1))) * (Nat.choose k (a + (m + 1)) : ℤ) : ℤ) : ℝ) *
            pairCorr f (k + r) (k + c) (a + (m + 1) + b) := by
      apply Finset.sum_congr rfl; intro m _
      have : a + 1 + m = a + (m + 1) := by omega
      rw [this]
    rw [hshift, hval (a + b) hvalid]
    simp only [Nat.add_zero]
    push_cast; ring

private lemma wellFormed_and_eval_psdBLoop5 {n : ℕ} (f : BooleanFun n)
    (val : ℕ → ℝ) (step base : ℕ)
    (hn : n < 32) (k r c bLo : ℕ) (scaleRC : ℤ)
    (hkn : 2 * k ≤ n) (hr : r ≤ n - 2 * k) (hc : c ≤ n - 2 * k)
    (hbLo : r + c - (n - 2 * k) ≤ bLo)
    (hval : ∀ t, ValidTriple n (k + r) (k + c) t →
      val (base + step * t) = pairCorr f (k + r) (k + c) t) :
    ∀ rem off tr,
      bLo + off + rem ≤ min r c + 1 → IntTrie.WellFormed 5 tr →
      IntTrie.WellFormed 5
          (psdBLoop5 (n - 2 * k) k r c bLo (scaleRC * (fastChoose (n - 2 * k) r : ℤ)) rem off tr) ∧
        IntTrie.evalTrie val step base
            (psdBLoop5 (n - 2 * k) k r c bLo (scaleRC * (fastChoose (n - 2 * k) r : ℤ)) rem off tr) =
          IntTrie.evalTrie val step base tr +
            (scaleRC : ℝ) *
              ∑ m ∈ Finset.range rem,
                (pairCount (n - 2 * k) r c (bLo + (off + m)) : ℝ) *
                  ∑ a ∈ Finset.range (k + 1),
                    (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                      pairCorr f (k + r) (k + c) (a + (bLo + (off + m)))
  | 0, _, tr, _, hwf => by simp [psdBLoop5, hwf]
  | rem + 1, off, tr, hlt, hwf => by
    simp only [psdBLoop5]
    set b := bLo + off
    set multB : ℤ := ((fastChoose r b * fastChoose (n - 2 * k - r) (c - b) : ℕ) : ℤ)
    obtain ⟨hwf1, hev1⟩ := wellFormed_and_eval_psdALoop5 f val step base hn k r c b
      (scaleRC * (fastChoose (n - 2 * k) r : ℤ) * multB) (by omega) (by omega) (by omega)
      (by omega) (by omega) hkn hval (k + 1) 0 1 tr (by omega) (by simp) hwf
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_psdBLoop5 f val step base hn k r c bLo scaleRC
      hkn hr hc hbLo hval rem (off + 1) _ (by omega) hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1]
    have houter :
        ∑ m ∈ Finset.range (rem + 1),
          (pairCount (n - 2 * k) r c (bLo + (off + m)) : ℝ) *
            ∑ a ∈ Finset.range (k + 1),
              (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                pairCorr f (k + r) (k + c) (a + (bLo + (off + m))) =
        (∑ m ∈ Finset.range rem,
          (pairCount (n - 2 * k) r c (bLo + (off + (m + 1))) : ℝ) *
            ∑ a ∈ Finset.range (k + 1),
              (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                pairCorr f (k + r) (k + c) (a + (bLo + (off + (m + 1))))) +
        (pairCount (n - 2 * k) r c (bLo + (off + 0)) : ℝ) *
          ∑ a ∈ Finset.range (k + 1),
            (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
              pairCorr f (k + r) (k + c) (a + (bLo + (off + 0))) :=
      Finset.sum_range_succ' _ rem
    rw [houter]
    have hshift :
        ∑ m ∈ Finset.range rem,
          (pairCount (n - 2 * k) r c (bLo + (off + 1 + m)) : ℝ) *
            ∑ a ∈ Finset.range (k + 1),
              (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                pairCorr f (k + r) (k + c) (a + (bLo + (off + 1 + m))) =
        ∑ m ∈ Finset.range rem,
          (pairCount (n - 2 * k) r c (bLo + (off + (m + 1))) : ℝ) *
            ∑ a ∈ Finset.range (k + 1),
              (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                pairCorr f (k + r) (k + c) (a + (bLo + (off + (m + 1)))) := by
      apply Finset.sum_congr rfl; intro m _
      have : off + 1 + m = off + (m + 1) := by omega
      rw [this]
    rw [hshift]
    have hmul3 : ((scaleRC * (fastChoose (n - 2 * k) r : ℤ) * multB : ℤ) : ℝ) =
        (scaleRC : ℝ) * (pairCount (n - 2 * k) r c b : ℝ) := by
      simp only [multB, fastChoose_eq, pairCount]; push_cast; ring
    simp only [Nat.add_zero, zero_add]
    rw [hmul3]; ring

private lemma wellFormed_and_eval_psdPairTrie {n : ℕ} (f : BooleanFun n)
    (hn : n < 32) (k r c : ℕ) (scaleRC : ℤ)
    (hkn : 2 * k ≤ n) (hr : r ≤ n - 2 * k) (hc : c ≤ n - 2 * k) :
    IntTrie.WellFormed 15 (psdPairTrie n k r c scaleRC) ∧
      IntTrie.evalTrie (terwMVal f) 1 0 (psdPairTrie n k r c scaleRC) =
        (scaleRC : ℝ) * bTilde k (fun x => boolToReal (f x)) r c := by
  unfold psdPairTrie
  by_cases hs : scaleRC = 0
  · subst hs; exact ⟨IntTrie.wellFormed_empty 15, by simp [IntTrie.evalTrie]⟩
  · have hbeq : (scaleRC == 0) = false := by simp [hs]
    rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
    set r' := min r c
    set c' := max r c
    have hr'c' : r' ≤ c' := min_le_max
    have hr' : r' ≤ n - 2 * k := min_le_of_left_le hr
    have hc' : c' ≤ n - 2 * k := max_le hr hc
    set bLo := r' + c' - (n - 2 * k)
    set bHi := min r' c'
    have hbLo_le : bLo ≤ bHi := by omega
    have hij_lt : (k + r') + 32 * (k + c') < 2 ^ 10 := by omega
    have hsum_b : (scaleRC : ℝ) *
        ∑ m ∈ Finset.range (bHi - bLo + 1),
          (pairCount (n - 2 * k) r' c' (bLo + (0 + m)) : ℝ) *
            ∑ a ∈ Finset.range (k + 1),
              (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                pairCorr f (k + r') (k + c') (a + (bLo + (0 + m))) =
        (scaleRC : ℝ) * bTilde k (fun x => boolToReal (f x)) r' c' := by
      congr 1
      unfold bTilde
      apply Finset.sum_nbij (fun m => bLo + m)
      · intro m hm; rw [Finset.mem_range] at hm; rw [Finset.mem_Icc]; omega
      · intro m₁ _ m₂ _ hEq; dsimp only at hEq; omega
      · intro b hb; rw [Finset.mem_coe, Finset.mem_Icc] at hb
        refine ⟨b - bLo, ?_, by dsimp only; omega⟩
        rw [Finset.mem_coe, Finset.mem_range]; omega
      · intro _ _; simp only [zero_add, pairCorrR_bool]
    have hb_eq : bTilde k (fun x => boolToReal (f x)) r' c' =
        bTilde k (fun x => boolToReal (f x)) r c := by
      by_cases hrc : r ≤ c
      · simp [r', c', min_eq_left hrc, max_eq_right hrc]
      · have hcr : c ≤ r := by omega
        simp only [r', c', min_eq_right hcr, max_eq_left hcr]
        exact bTilde_comm f k c r hkn hc hr
    have hmod := IntTrie.wellFormed_and_eval_modifyAt (terwMVal f) 10 5
      ((k + r') + 32 * (k + c')) 1 0
      ((scaleRC : ℝ) * bTilde k (fun x => boolToReal (f x)) r' c')
      (psdBLoop5 (n - 2 * k) k r' c' bLo (scaleRC * (fastChoose (n - 2 * k) r' : ℤ)) (bHi - bLo + 1) 0)
      .empty hij_lt (IntTrie.wellFormed_empty 15) (by
        intro s hs
        have hval_m : ∀ t, ValidTriple n (k + r') (k + c') t →
            terwMVal f ((k + r') + 32 * (k + c') + 1024 * t) = pairCorr f (k + r') (k + c') t := by
          intro t hvt
          have hkey_eq : (k + r') + 32 * (k + c') + 1024 * t = canonMKey (k + r') (k + c') t := by
            unfold canonMKey
            have hle : k + r' ≤ k + c' := by omega
            simp only [hle, ↓reduceIte]; ring
          rw [hkey_eq, terwMVal_canonMKey f hn hvt]
        obtain ⟨hwfB, hevB⟩ := wellFormed_and_eval_psdBLoop5 f (terwMVal f) 1024
          ((k + r') + 32 * (k + c')) hn k r' c' bLo scaleRC
          hkn hr' hc' (le_refl _) hval_m (bHi - bLo + 1) 0 s (by omega) hs
        refine ⟨hwfB, ?_⟩
        simp only [zero_add, one_mul, mul_one]
        have hpow : (2 ^ 10 : ℕ) = 1024 := by decide
        rw [hpow, hevB, hsum_b])
    refine ⟨hmod.1, ?_⟩
    rw [hmod.2, hb_eq]
    simp [IntTrie.evalTrie]

private lemma wellFormed_and_eval_psdUpperInner {n : ℕ} (f : BooleanFun n)
    (hn : n < 32) (k r : ℕ) (wr : ℤ) (hkn : 2 * k ≤ n) (hr : r ≤ n - 2 * k) :
    ∀ l, (∀ q ∈ l, q.1 ≤ n - 2 * k) →
      IntTrie.WellFormed 15 (psdUpperInner n k r wr l) ∧
        IntTrie.evalTrie (terwMVal f) 1 0 (psdUpperInner n k r wr l) =
          (l.map (fun q => 2 * (wr : ℝ) * (q.2 : ℝ) *
            bTilde k (fun x => boolToReal (f x)) r q.1)).sum
  | [], _ => ⟨IntTrie.wellFormed_empty 15, by simp [psdUpperInner, IntTrie.evalTrie]⟩
  | (c, wc) :: tl, hall => by
    simp only [psdUpperInner, List.map_cons, List.sum_cons]
    have hc : c ≤ n - 2 * k := hall (c, wc) (List.mem_cons_self ..)
    obtain ⟨hwf1, hev1⟩ := wellFormed_and_eval_psdPairTrie f hn k r c (2 * wr * wc) hkn hr hc
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_psdUpperInner f hn k r wr hkn hr tl
      (fun q hq => hall q (List.mem_cons_of_mem _ hq))
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_merge (terwMVal f) 15 1 0 _ _ hwf1 hwf2
    refine ⟨hwfM, ?_⟩
    rw [hevM, hev1, hev2]; push_cast; ring

private lemma wellFormed_and_eval_psdUpperTrie {n : ℕ} (f : BooleanFun n)
    (hn : n < 32) (k : ℕ) (hkn : 2 * k ≤ n) :
    ∀ w, (∀ p ∈ w, p.1 ≤ n - 2 * k) →
      IntTrie.WellFormed 15 (psdUpperTrie n k w) ∧
        IntTrie.evalTrie (terwMVal f) 1 0 (psdUpperTrie n k w) = evalPsdList k f w
  | [], _ => ⟨IntTrie.wellFormed_empty 15, by simp [psdUpperTrie, evalPsdList, IntTrie.evalTrie]⟩
  | (r, wr) :: tl, hall => by
    have hr : r ≤ n - 2 * k := hall (r, wr) (List.mem_cons_self ..)
    have htl : ∀ q ∈ tl, q.1 ≤ n - 2 * k := fun q hq => hall q (List.mem_cons_of_mem _ hq)
    obtain ⟨hwfD, hevD⟩ := wellFormed_and_eval_psdPairTrie f hn k r r (wr * wr) hkn hr hr
    obtain ⟨hwfI, hevI⟩ := wellFormed_and_eval_psdUpperInner f hn k r wr hkn hr tl htl
    obtain ⟨hwfT, hevT⟩ := wellFormed_and_eval_psdUpperTrie f hn k hkn tl htl
    obtain ⟨hwfM1, hevM1⟩ := IntTrie.wellFormed_and_eval_merge (terwMVal f) 15 1 0 _ _ hwfD hwfI
    obtain ⟨hwfM2, hevM2⟩ := IntTrie.wellFormed_and_eval_merge (terwMVal f) 15 1 0 _ _ hwfM1 hwfT
    refine ⟨hwfM2, ?_⟩
    dsimp only [psdUpperTrie]
    rw [hevM2, hevM1, hevD, hevI, hevT]
    unfold evalPsdList
    simp only [List.map_cons, List.sum_cons]
    have hsplit : (tl.map (fun p =>
        ((p.2 : ℝ) * (wr : ℝ) * bTilde k (fun x => boolToReal (f x)) p.1 r) +
        (tl.map (fun q => (p.2 : ℝ) * (q.2 : ℝ) *
          bTilde k (fun x => boolToReal (f x)) p.1 q.1)).sum)).sum =
      (tl.map (fun p => (p.2 : ℝ) * (wr : ℝ) * bTilde k (fun x => boolToReal (f x)) p.1 r)).sum +
      (tl.map (fun p => (tl.map (fun q => (p.2 : ℝ) * (q.2 : ℝ) *
        bTilde k (fun x => boolToReal (f x)) p.1 q.1)).sum)).sum := by
      have hadd : ∀ (l : List (ℕ × ℤ)) (g₁ g₂ : ℕ × ℤ → ℝ),
          (l.map (fun p => g₁ p + g₂ p)).sum = (l.map g₁).sum + (l.map g₂).sum := by
        intro l g₁ g₂
        induction l with
        | nil => simp
        | cons a rest ih => simp only [List.map_cons, List.sum_cons]; linarith
      exact hadd tl _ _
    have hsym : (tl.map (fun p => (p.2 : ℝ) * (wr : ℝ) * bTilde k (fun x => boolToReal (f x)) p.1 r)).sum =
        (tl.map (fun q => (wr : ℝ) * (q.2 : ℝ) * bTilde k (fun x => boolToReal (f x)) r q.1)).sum := by
      congr 1; apply List.map_congr_left; intro q hq
      rw [bTilde_comm f k q.1 r hkn (htl q hq) hr]; ring
    have hdbl : (tl.map (fun q => 2 * (wr : ℝ) * (q.2 : ℝ) *
        bTilde k (fun x => boolToReal (f x)) r q.1)).sum =
      2 * (tl.map (fun q => (wr : ℝ) * (q.2 : ℝ) *
        bTilde k (fun x => boolToReal (f x)) r q.1)).sum := by
      clear hevD hevI hevT hevM1 hevM2 hwfD hwfI hwfT hwfM1 hwfM2 htl hall hsplit hsym
      induction tl with
      | nil => simp
      | cons a rest ih => simp only [List.map_cons, List.sum_cons]; linarith
    rw [hsplit, hsym, hdbl]
    push_cast; ring

private lemma expandMTrieAux_sound {n d : ℕ} (f : BooleanFun n)
    (hn : n < 32) (hd : d < 16)
    (c : ℕ → ℕ → ℕ → ℝ)
    (hc : ∀ j ≤ n, ∀ a b, a ≤ j → b ≤ n - j →
      pairCorr f (a + b) j a =
        ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ)) :
    let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
    ∀ (t : IntTrie) (step base : ℕ),
      (expandMTrieAux n d step base t).1 = true →
      IntTrie.WellFormed 14 (expandMTrieAux n d step base t).2 ∧
        IntTrie.evalTrie cVal 1 0 (expandMTrieAux n d step base t).2 =
          IntTrie.evalTrie (terwMVal f) step base t := by
  intro cVal t
  induction t with
  | empty =>
    intro step base _
    exact ⟨trivial, by simp [expandMTrieAux, IntTrie.evalTrie]⟩
  | leaf v =>
    intro step base hok
    simp only [expandMTrieAux] at hok ⊢
    by_cases hv : v = 0
    · subst hv; exact ⟨IntTrie.wellFormed_empty 14, by simp [IntTrie.evalTrie]⟩
    · have hbeq : (v == 0) = false := by simp [hv]
      rw [hbeq] at hok ⊢; simp only [Bool.false_eq_true, ↓reduceIte] at hok ⊢
      split_ifs at hok ⊢ with hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hij, hvt⟩ := hcond
      have hvalid := (validTripleB_iff n (base % 32) ((base / 32) % 32) (base / 1024)).mp hvt
      obtain ⟨hin, hjn, hti, htj, hij_n⟩ := hvalid
      obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalH c n d ((base / 32) % 32) (base / 1024)
        (base % 32 - base / 1024) v .empty (by omega) hd hjn htj (by omega) trivial
      refine ⟨hwfC, ?_⟩
      dsimp only
      rw [hevC]; simp only [IntTrie.evalTrie, zero_add]
      have hcorr : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c ((base / 32) % 32) r s * (Nat.choose (base / 1024) r : ℝ) *
            (Nat.choose (base % 32 - base / 1024) s : ℝ) = terwMVal f base := by
        rw [← hc ((base / 32) % 32) hjn (base / 1024) (base % 32 - base / 1024) htj (by omega),
          Nat.add_sub_of_le hti]
        rfl
      rw [hcorr]
  | node lo hi ihlo ihhi =>
    intro step base hok
    simp only [expandMTrieAux, Bool.and_eq_true] at hok ⊢
    obtain ⟨hwf1, hev1⟩ := ihlo (2 * step) base hok.1
    obtain ⟨hwf2, hev2⟩ := ihhi (2 * step) (base + step) hok.2
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_merge cVal 14 1 0 _ _ hwf1 hwf2
    refine ⟨hwfM, ?_⟩
    rw [hevM, hev1, hev2]; simp [IntTrie.evalTrie]

private lemma psdStep_sound {n d : ℕ} (f : BooleanFun n)
    (hn : n < 32) (hd : d < 16)
    (S : ℕ → ℕ) (hS : ∀ k ≤ n, realLayerSum (fun x => boolToReal (f x)) k = (S k : ℝ))
    (c : ℕ → ℕ → ℕ → ℝ)
    (hc : ∀ j ≤ n, ∀ a b, a ≤ j → b ≤ n - j →
      pairCorr f (a + b) j a =
        ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ))
    (step : PsdBinoStep) (hok : psdStepOk n step = true) :
    let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
    IntTrie.WellFormed 14 (psdStepC n d step) ∧
      IntTrie.WellFormed 15 (psdStepM n step) ∧
      (psdStepObj n S step : ℝ) ≤
        IntTrie.evalTrie cVal 1 0 (psdStepC n d step) +
        IntTrie.evalTrie (terwMVal f) 1 0 (psdStepM n step) := by
  intro cVal
  have hcmul : ∀ k ≤ n, (Nat.choose n k : ℝ) * layerAvg (fun x => boolToReal (f x)) k = (S k : ℝ) := by
    intro k hk
    have hpos : (Nat.choose n k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    rw [layerAvg, mul_div_cancel₀ _ hpos, hS k hk]
  cases step with
  | eqSym i j t μ =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    obtain ⟨hin, hjn, hti, htj, hij⟩ := hvalid
    obtain ⟨hwfC1, hevC1⟩ := wellFormed_and_eval_addEvalH c n d j t (i - t) μ .empty (by omega) hd
      hjn htj (by omega) trivial
    obtain ⟨hwfC2, hevC2⟩ := wellFormed_and_eval_addEvalH c n d i t (j - t) (-μ) _ (by omega) hd
      hin hti (by omega) hwfC1
    have h1 : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
        c j r s * (Nat.choose t r : ℝ) * (Nat.choose (i - t) s : ℝ) = pairCorr f i j t := by
      rw [← hc j hjn t (i - t) htj (by omega), Nat.add_sub_of_le hti]
    have h2 : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
        c i r s * (Nat.choose t r : ℝ) * (Nat.choose (j - t) s : ℝ) = pairCorr f j i t := by
      rw [← hc i hin t (j - t) hti (by omega), Nat.add_sub_of_le htj]
    refine ⟨hwfC2, trivial, ?_⟩
    dsimp only [psdStepObj, psdStepC, psdStepM]
    rw [hevC2, hevC1, h1, h2, pairCorr_symm f ⟨hin, hjn, hti, htj, hij⟩]
    simp only [IntTrie.evalTrie]; push_cast; linarith
  | eqDiag i μ =>
    simp only [psdStepOk, decide_eq_true_eq] at hok
    have hvalid : ValidTriple n i i i := ⟨hok, hok, le_refl i, le_refl i, by omega⟩
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i i i) 1 0
      (μ * (fastChoose n i : ℤ)) .empty (canonMKey_lt _ _ _ (by omega) (by omega) (by omega)) trivial
    refine ⟨trivial, hwfM, ?_⟩
    dsimp only [psdStepObj, psdStepC, psdStepM]
    rw [hevM]; simp only [IntTrie.evalTrie, zero_add, one_mul, fastChoose_eq,
      terwMVal_canonMKey f hn hvalid, pairCorr_diag f hok]
    have := hcmul i hok
    push_cast; linear_combination -(μ : ℝ) * this
  | eqHyp i j μ =>
    simp only [psdStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hin, hjn⟩ := hok
    set tLo := i + j - n
    set tHi := min i j
    have htLo_le : tLo ≤ tHi := by omega
    obtain ⟨hwfM, hevM⟩ := wellFormed_and_eval_addHypLoop f hn i j tLo (μ * (fastChoose n i : ℤ))
      hin hjn (le_refl _) (tHi - tLo + 1) 0 .empty (by omega) trivial
    have hsum_eq :
        ∑ m ∈ Finset.range (tHi - tLo + 1),
          (Nat.choose i (tLo + (0 + m)) * Nat.choose (n - i) (j - (tLo + (0 + m))) : ℝ) *
            pairCorr f i j (tLo + (0 + m)) =
        ∑ tv ∈ Finset.Icc tLo tHi,
          (Nat.choose i tv * Nat.choose (n - i) (j - tv) : ℝ) * pairCorr f i j tv := by
      apply Finset.sum_nbij (fun m => tLo + m)
      · intro m hm; rw [Finset.mem_range] at hm; rw [Finset.mem_Icc]; omega
      · intro m₁ _ m₂ _ hEq; dsimp only at hEq; omega
      · intro tv htv; rw [Finset.mem_coe, Finset.mem_Icc] at htv
        refine ⟨tv - tLo, ?_, by dsimp only; omega⟩
        rw [Finset.mem_coe, Finset.mem_range]; omega
      · intro _ _; simp only [zero_add]
    have hprod := sum_pairCorr_layerProd f hin hjn
    have hterm : ((μ * (fastChoose n i : ℤ) : ℤ) : ℝ) *
        ∑ m ∈ Finset.range (tHi - tLo + 1),
          (Nat.choose i (tLo + (0 + m)) * Nat.choose (n - i) (j - (tLo + (0 + m))) : ℝ) *
            pairCorr f i j (tLo + (0 + m)) = (μ : ℝ) * ((S i * S j : ℕ) : ℝ) := by
      rw [hsum_eq, hprod, fastChoose_eq]; push_cast
      calc (μ : ℝ) * (Nat.choose n i : ℝ) *
            ((Nat.choose n j : ℝ) * layerAvg (fun x => boolToReal (f x)) i *
              layerAvg (fun x => boolToReal (f x)) j)
          = (μ : ℝ) * (((Nat.choose n i : ℝ) * layerAvg (fun x => boolToReal (f x)) i) *
              ((Nat.choose n j : ℝ) * layerAvg (fun x => boolToReal (f x)) j)) := by ring
        _ = (μ : ℝ) * ((S i : ℝ) * (S j : ℝ)) := by rw [hcmul i hin, hcmul j hjn]
    refine ⟨trivial, hwfM, ?_⟩
    dsimp only [psdStepObj, psdStepC, psdStepM]
    change ((μ * ((S i * S j : ℕ) : ℤ) : ℤ) : ℝ) ≤
      IntTrie.evalTrie cVal 1 0 .empty +
      IntTrie.evalTrie (terwMVal f) 1 0
        (addHypLoop n i j tLo (μ * (fastChoose n i : ℤ)) (tHi - tLo + 1) 0 .empty)
    rw [hevM, hterm]; simp only [IntTrie.evalTrie]; push_cast; linarith
  | ubMLo0 i j t lam =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t) 1 0
      (lam : ℤ) .empty (canonMKey_lt _ _ _ (by have := hvalid.1; omega)
        (by have := hvalid.2.1; omega) (by have := hvalid.1; have := hvalid.2.2.1; omega)) trivial
    have hnn : 0 ≤ pairCorr f i j t := pairCorr_nonneg f
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨trivial, hwfM, ?_⟩
    dsimp only [psdStepObj, psdStepC, psdStepM]
    rw [hevM]; simp only [IntTrie.evalTrie, zero_add, one_mul, terwMVal_canonMKey f hn hvalid]
    push_cast; nlinarith
  | ubMMcc i j t lam =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    have hin : i ≤ n := hvalid.1
    have hjn : j ≤ n := hvalid.2.1
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t) 1 0
      ((lam : ℤ) * ((fastChoose n i : ℤ) * (fastChoose n j : ℤ))) .empty
      (canonMKey_lt _ _ _ (by omega) (by omega) (by have := hvalid.2.2.1; omega)) trivial
    have hmcc : layerAvg (fun x => boolToReal (f x)) i +
        layerAvg (fun x => boolToReal (f x)) j - pairCorr f i j t ≤ 1 := pairCorr_frechet f hvalid
    have hci : (0 : ℝ) ≤ (Nat.choose n i : ℝ) := Nat.cast_nonneg _
    have hcj : (0 : ℝ) ≤ (Nat.choose n j : ℝ) := Nat.cast_nonneg _
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    have hscaled : (S i : ℝ) * (Nat.choose n j : ℝ) + (S j : ℝ) * (Nat.choose n i : ℝ) -
        (Nat.choose n i : ℝ) * (Nat.choose n j : ℝ) ≤
        (Nat.choose n i : ℝ) * (Nat.choose n j : ℝ) * pairCorr f i j t := by
      rw [← hcmul i hin, ← hcmul j hjn]
      have hprod_nn : (0 : ℝ) ≤ (Nat.choose n i : ℝ) * (Nat.choose n j : ℝ) := mul_nonneg hci hcj
      nlinarith
    refine ⟨trivial, hwfM, ?_⟩
    dsimp only [psdStepObj, psdStepC, psdStepM]
    rw [hevM]; simp only [IntTrie.evalTrie, zero_add, one_mul, fastChoose_eq,
      terwMVal_canonMKey f hn hvalid]
    push_cast; nlinarith
  | ubMLePi i j t lam =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    have hin : i ≤ n := hvalid.1
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t) 1 0
      (-(lam : ℤ) * (fastChoose n i : ℤ)) .empty
      (canonMKey_lt _ _ _ (by omega) (by have := hvalid.2.1; omega) (by have := hvalid.2.2.1; omega)) trivial
    have hle := pairCorr_le_left f hvalid
    have hci : (0 : ℝ) ≤ (Nat.choose n i : ℝ) := Nat.cast_nonneg _
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    have hscaled : (Nat.choose n i : ℝ) * pairCorr f i j t ≤ (S i : ℝ) := by
      rw [← hcmul i hin]; nlinarith
    refine ⟨trivial, hwfM, ?_⟩
    dsimp only [psdStepObj, psdStepC, psdStepM]
    rw [hevM]; simp only [IntTrie.evalTrie, zero_add, one_mul, fastChoose_eq,
      terwMVal_canonMKey f hn hvalid]
    push_cast; nlinarith
  | ubMLePj i j t lam =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    have hjn : j ≤ n := hvalid.2.1
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t) 1 0
      (-(lam : ℤ) * (fastChoose n j : ℤ)) .empty
      (canonMKey_lt _ _ _ (by have := hvalid.1; omega) (by omega) (by have := hvalid.2.2.2.1; omega)) trivial
    have hle := pairCorr_le_right f hvalid
    have hcj : (0 : ℝ) ≤ (Nat.choose n j : ℝ) := Nat.cast_nonneg _
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    have hscaled : (Nat.choose n j : ℝ) * pairCorr f i j t ≤ (S j : ℝ) := by
      rw [← hcmul j hjn]; nlinarith
    refine ⟨trivial, hwfM, ?_⟩
    dsimp only [psdStepObj, psdStepC, psdStepM]
    rw [hevM]; simp only [IntTrie.evalTrie, zero_add, one_mul, fastChoose_eq,
      terwMVal_canonMKey f hn hvalid]
    push_cast; nlinarith
  | ubPsd k w lam =>
    simp only [psdStepOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
    obtain ⟨hkn, hw⟩ := hok
    have hw' : ∀ p ∈ w, p.1 ≤ n - 2 * k := fun p hp => by simpa using hw p hp
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_psdUpperTrie f hn k hkn w hw'
    obtain ⟨hwfM, hevM⟩ := wellFormed_and_eval_scaleTrie (terwMVal f) 15 (lam : ℤ) 1 0 _ hwfU
    have hpsd := evalPsdList_nonneg hkn f w hw'
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨trivial, hwfM, ?_⟩
    dsimp only [psdStepObj, psdStepC, psdStepM]
    rw [hevM, hevU]; simp only [IntTrie.evalTrie, zero_add, Int.cast_zero, Int.cast_natCast]
    exact mul_nonneg hlam hpsd

private lemma psdTree_sound {n d : ℕ} (f : BooleanFun n)
    (hn : n < 32) (hd : d < 16) (hf : polyDegree f ≤ d)
    (S : ℕ → ℕ) (hS : ∀ k ≤ n, realLayerSum (fun x => boolToReal (f x)) k = (S k : ℝ))
    (tree : BinTree PsdBinoStep) (hok : tree.all (psdStepOk n) = true) :
    ∃ c : ℕ → ℕ → ℕ → ℝ,
      (∀ j ≤ n, ∀ a b, a ≤ j → b ≤ n - j →
        pairCorr f (a + b) j a =
          ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
            c j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ)) ∧
      IntTrie.WellFormed 14 (IntTrie.mergeTree (psdStepC n d) tree) ∧
      IntTrie.WellFormed 15 (IntTrie.mergeTree (psdStepM n) tree) ∧
      (tree.sumZ (psdStepObj n S) : ℝ) ≤
        IntTrie.evalTrie (fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)) 1 0
          (IntTrie.mergeTree (psdStepC n d) tree) +
        IntTrie.evalTrie (terwMVal f) 1 0 (IntTrie.mergeTree (psdStepM n) tree) := by
  have hc_ex : ∀ j : ℕ, ∃ cj : ℕ → ℕ → ℝ,
      j ≤ n → ∀ a b, a ≤ j → b ≤ n - j →
        pairCorr f (a + b) j a =
          ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
            cj r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨cj, hcj⟩ := pairCorr_eq_bivar_binomial_sum f hf hj
      exact ⟨cj, fun _ => hcj⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hj⟩
  choose c hc using hc_ex
  refine ⟨c, hc, ?_⟩
  let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
  induction tree with
  | empty =>
    exact ⟨trivial, trivial, by simp [BinTree.sumZ, IntTrie.mergeTree, IntTrie.evalTrie]⟩
  | leaf s =>
    exact psdStep_sound f hn hd S hS c hc s hok
  | node l r ihl ihr =>
    simp only [BinTree.all, Bool.and_eq_true] at hok
    obtain ⟨hwfCl, hwfMl, hlel⟩ := ihl hok.1
    obtain ⟨hwfCr, hwfMr, hler⟩ := ihr hok.2
    obtain ⟨hwfC, hevC⟩ := IntTrie.wellFormed_and_eval_merge cVal 14 1 0 _ _ hwfCl hwfCr
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_merge (terwMVal f) 15 1 0 _ _ hwfMl hwfMr
    refine ⟨hwfC, hwfM, ?_⟩
    dsimp only [BinTree.sumZ, IntTrie.mergeTree]
    rw [hevC, hevM]; push_cast; linarith

/-- **Soundness of Step-3 PSD+Binomial Farkas Infeasibility Checker**:
Proves no Boolean function `f : BooleanFun n` of degree `≤ d` has layer sums `S`. -/
theorem false_of_psd_bino_farkas {n d : ℕ} (f : BooleanFun n)
    (hf : polyDegree f ≤ d)
    (S : ℕ → ℕ) (hS : ∀ k ≤ n, realLayerSum (fun x => boolToReal (f x)) k = (S k : ℝ))
    (tree : BinTree PsdBinoStep)
    (hcert : checkPsdBinoFarkas n d S tree = true) : False := by
  unfold checkPsdBinoFarkas at hcert
  split_ifs at hcert with hnd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hnd hcert
  obtain ⟨hn, hd⟩ := hnd
  obtain ⟨⟨⟨hok, hmOk⟩, hc0⟩, hpos⟩ := hcert
  obtain ⟨c, hc, hwfC, _, hle⟩ := psdTree_sound f hn hd hf S hS tree hok
  let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
  obtain ⟨hwfFromM, hevFromM⟩ :=
    expandMTrieAux_sound f hn hd c hc (IntTrie.mergeTree (psdStepM n) tree) 1 0 hmOk
  obtain ⟨_, hevAll⟩ := IntTrie.wellFormed_and_eval_merge cVal 14 1 0 _ _ hwfC hwfFromM
  rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hc0] at hevAll
  have hposR : (0 : ℝ) < (tree.sumZ (psdStepObj n S) : ℝ) := by exact_mod_cast hpos
  dsimp only [cVal] at hevAll hevFromM
  linarith

/-- **Soundness of Step-3 PSD+Binomial Linear Bound Checker**:
Proves `(expectedLb : ℝ) ≤ (scale : ℝ) * evalTargetM f targetM`. -/
theorem targetM_bound_of_psd_bino_cert {n d : ℕ} (f : BooleanFun n)
    (hf : polyDegree f ≤ d)
    (S : ℕ → ℕ) (hS : ∀ k ≤ n, realLayerSum (fun x => boolToReal (f x)) k = (S k : ℝ))
    (tree : BinTree PsdBinoStep)
    (targetM : List (ℕ × ℕ × ℕ × ℤ)) (scale : ℕ) (expectedLb : ℤ)
    (hcert : checkPsdBinoBound n d S tree targetM scale expectedLb = true) :
    (expectedLb : ℝ) ≤ (scale : ℝ) * evalTargetM f targetM := by
  unfold checkPsdBinoBound at hcert
  split_ifs at hcert with hcond
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcond hcert
  obtain ⟨⟨hn, hd⟩, htm⟩ := hcond
  obtain ⟨⟨⟨hok, hmOk⟩, hc0⟩, hlb⟩ := hcert
  obtain ⟨c, hc, hwfC, hwfM, hle⟩ := psdTree_sound f hn hd hf S hS tree hok
  let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
  have htm' : ∀ q ∈ targetM, ValidTriple n q.1 q.2.1 q.2.2.1 :=
    fun q hq => (validTripleB_iff n q.1 q.2.1 q.2.2.1).mp (htm q hq)
  obtain ⟨_, hevSub⟩ := wellFormed_and_eval_addMList f hn (-(scale : ℤ)) targetM
    (IntTrie.mergeTree (psdStepM n) tree) htm' hwfM
  obtain ⟨hwfFromM, hevFromM⟩ :=
    expandMTrieAux_sound f hn hd c hc
      (addMList (-(scale : ℤ)) targetM (IntTrie.mergeTree (psdStepM n) tree)) 1 0 hmOk
  obtain ⟨_, hevAll⟩ := IntTrie.wellFormed_and_eval_merge cVal 14 1 0 _ _ hwfC hwfFromM
  rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hc0] at hevAll
  have hlbR : (expectedLb : ℝ) ≤ (tree.sumZ (psdStepObj n S) : ℝ) := by exact_mod_cast hlb
  push_cast at hevSub
  dsimp only [cVal] at hevAll hevFromM
  linarith

/-! ### Part 3: `j`-Sliced Low-Memory Step-3 Verifier (Depth-10 `mTrie` → Depth-8 `cTrie`) -/

/-- Layer-`jTarget` pair-correlation lookup for a depth-10 `IntTrie` keyed by `min i j + 32 * t`. -/
noncomputable def mValForJ {n : ℕ} (f : BooleanFun n) (jTarget idx : ℕ) : ℝ :=
  pairCorr f (idx % 32) jTarget (idx / 32)

/-- Layer-sliced hypergeometric accumulator (depth-10 `IntTrie` keyed by `min i j + 32 * tv`). -/
def addHypLoopForJ (n i j tLo : ℕ) (scale : ℤ) : ℕ → ℕ → IntTrie → IntTrie
  | 0, _, t => t
  | rem + 1, off, t =>
      let tv := tLo + off
      let w : ℤ := ((fastChoose i tv * fastChoose (n - i) (j - tv) : ℕ) : ℤ)
      let t' := IntTrie.addAt 10 (min i j + 32 * tv) (scale * w) t
      addHypLoopForJ n i j tLo scale rem (off + 1) t'

/-- Layer-sliced target `m`-list accumulator (depth-10 `IntTrie`). -/
def addMListForJ (jTarget : ℕ) (scale : ℤ) : List (ℕ × ℕ × ℕ × ℤ) → IntTrie → IntTrie
  | [], t => t
  | (i, j, tv, c) :: rest, t =>
      let t' := if max i j == jTarget then
        IntTrie.addAt 10 (min i j + 32 * tv) (scale * c) t
      else t
      addMListForJ jTarget scale rest t'

/-- Layer-sliced `(r, c)` entry of `bTilde k`: empty unless `k + max r c == jTarget`. -/
def psdPairTrieForJ (n k jTarget r c : ℕ) (scaleRC : ℤ) : IntTrie :=
  if scaleRC == 0 || !(k + max r c == jTarget) then .empty
  else
    let r' := min r c
    let c' := max r c
    let n2k := n - 2 * k
    let bLo := r' + c' - n2k
    let bHi := min r' c'
    let scaleRC_cN2kR := scaleRC * (fastChoose n2k r' : ℤ)
    IntTrie.modifyAt 5 (k + r')
      (psdBLoop5 n2k k r' c' bLo scaleRC_cN2kR (bHi - bLo + 1) 0) .empty

/-- Layer-sliced upper-triangular off-diagonal PSD inner loop. -/
def psdUpperInnerForJ (n k jTarget r : ℕ) (wr : ℤ) : List (ℕ × ℤ) → IntTrie
  | [] => .empty
  | (c, wc) :: tl =>
      IntTrie.merge (psdPairTrieForJ n k jTarget r c (2 * wr * wc))
        (psdUpperInnerForJ n k jTarget r wr tl)

/-- Layer-sliced unscaled `w^T B̃^(k) w` restricted to layer `jTarget` (depth-10 `IntTrie`). -/
def psdUpperTrieForJ (n k jTarget : ℕ) : List (ℕ × ℤ) → IntTrie
  | [] => .empty
  | (r, wr) :: tl =>
      IntTrie.merge
        (IntTrie.merge (psdPairTrieForJ n k jTarget r r (wr * wr))
          (psdUpperInnerForJ n k jTarget r wr tl))
        (psdUpperTrieForJ n k jTarget tl)

/-- Layer-sliced direct `cTrie` contribution of `PsdBinoStep` (depth-8 `IntTrie`). -/
def psdStepCForJ (n d jTarget : ℕ) : PsdBinoStep → IntTrie
  | .eqSym i j t μ =>
      IntTrie.merge
        (if j == jTarget then addEvalHJ n d j t (i - t) μ .empty else .empty)
        (if i == jTarget then addEvalHJ n d i t (j - t) (-μ) .empty else .empty)
  | _ => .empty

/-- Layer-sliced `mTrie` contribution of `PsdBinoStep` (depth-10 `IntTrie`). -/
def psdStepMForJ (n jTarget : ℕ) : PsdBinoStep → IntTrie
  | .eqSym _ _ _ _ => .empty
  | .eqDiag i μ =>
      if i == jTarget then
        IntTrie.addAt 10 (i + 32 * i) (μ * (fastChoose n i : ℤ)) .empty
      else .empty
  | .eqHyp i j μ =>
      if max i j == jTarget then
        let tLo := i + j - n
        let tHi := min i j
        addHypLoopForJ n i j tLo (μ * (fastChoose n i : ℤ)) (tHi - tLo + 1) 0 .empty
      else .empty
  | .ubMLo0 i j t lam =>
      if max i j == jTarget then
        IntTrie.addAt 10 (min i j + 32 * t) (lam : ℤ) .empty
      else .empty
  | .ubMMcc i j t lam =>
      if max i j == jTarget then
        let cni : ℤ := (fastChoose n i : ℤ)
        let cnj : ℤ := (fastChoose n j : ℤ)
        IntTrie.addAt 10 (min i j + 32 * t) ((lam : ℤ) * (cni * cnj)) .empty
      else .empty
  | .ubMLePi i j t lam =>
      if max i j == jTarget then
        IntTrie.addAt 10 (min i j + 32 * t) (-(lam : ℤ) * (fastChoose n i : ℤ)) .empty
      else .empty
  | .ubMLePj i j t lam =>
      if max i j == jTarget then
        IntTrie.addAt 10 (min i j + 32 * t) (-(lam : ℤ) * (fastChoose n j : ℤ)) .empty
      else .empty
  | .ubPsd k w lam =>
      if decide (k ≤ jTarget) && decide (jTarget ≤ n - k) then
        scaleTrie (lam : ℤ) (psdUpperTrieForJ n k jTarget w)
      else .empty

/-- Layer-sliced stage-2 expansion of a depth-10 `mTrie` into a depth-8 `cTrie`. -/
def expandMTrieForJ (n d jTarget : ℕ) : ℕ → ℕ → IntTrie → Bool × IntTrie
  | _, _, .empty => (true, .empty)
  | _, base, .leaf v =>
      if v == 0 then (true, .empty)
      else
        let i := base % 32
        let t := base / 32
        if decide (i ≤ jTarget) && validTripleB n i jTarget t then
          (true, addEvalHJ n d jTarget t (i - t) v .empty)
        else (false, .empty)
  | step, base, .node lo hi =>
      let (ok1, c1) := expandMTrieForJ n d jTarget (2 * step) base lo
      let (ok2, c2) := expandMTrieForJ n d jTarget (2 * step) (base + step) hi
      (ok1 && ok2, IntTrie.merge c1 c2)

/-- Header + side-conditions + strict positivity check for a `j`-sliced Step-3 Farkas cert. -/
def checkPsdBinoFarkasHeader (n d : ℕ) (S : ℕ → ℕ) (tree : BinTree PsdBinoStep) : Bool :=
  decide (n < 32) && decide (d < 16) &&
    tree.all (psdStepOk n) &&
    decide (0 < tree.sumZ (psdStepObj n S))

/-- Header + side-conditions + target-bound check for a `j`-sliced Step-3 LP bound cert. -/
def checkPsdBinoBoundHeader (n d : ℕ) (S : ℕ → ℕ) (tree : BinTree PsdBinoStep)
    (targetM : List (ℕ × ℕ × ℕ × ℤ)) (expectedLb : ℤ) : Bool :=
  decide (n < 32) && decide (d < 16) &&
    targetM.all (fun q => validTripleB n q.1 q.2.1 q.2.2.1) &&
    tree.all (psdStepOk n) &&
    decide (expectedLb ≤ tree.sumZ (psdStepObj n S))

/-- Check a single layer slice `jTarget` for a Step-3 PSD+Binomial certificate. -/
def checkPsdBinoSlice (n d jTarget : ℕ) (tree : BinTree PsdBinoStep)
    (targetM : List (ℕ × ℕ × ℕ × ℤ)) (scale : ℕ) : Bool :=
  let mRaw := IntTrie.mergeTree (psdStepMForJ n jTarget) tree
  let mSub := if scale == 0 then mRaw else addMListForJ jTarget (-(scale : ℤ)) targetM mRaw
  let (mOk, cFromM) := expandMTrieForJ n d jTarget 1 0 mSub
  let cAll := IntTrie.merge (IntTrie.mergeTree (psdStepCForJ n d jTarget) tree) cFromM
  mOk && cAll.isZero

private lemma mValForJ_key {n : ℕ} (f : BooleanFun n) (hn : n < 32) {i j t : ℕ}
    (h : ValidTriple n i j t) :
    mValForJ f (max i j) (min i j + 32 * t) = pairCorr f i j t := by
  obtain ⟨hi, hj, hti, htj, hij⟩ := h
  have h1 : (min i j + 32 * t) % 32 = min i j := by omega
  have h2 : (min i j + 32 * t) / 32 = t := by omega
  simp only [mValForJ, h1, h2]
  by_cases hle : i ≤ j
  · rw [min_eq_left hle, max_eq_right hle]
  · have hji : j ≤ i := by omega
    rw [min_eq_right hji, max_eq_left hji]
    exact pairCorr_symm f ⟨hj, hi, htj, hti, by omega⟩

private lemma wellFormed_and_eval_addHypLoopForJ {n : ℕ} (f : BooleanFun n) (hn : n < 32)
    (i j tLo : ℕ) (scale : ℤ) (hi : i ≤ n) (hj : j ≤ n) (htLo : i + j - n ≤ tLo) :
    ∀ rem off tr,
      tLo + off + rem ≤ min i j + 1 → IntTrie.WellFormed 10 tr →
      IntTrie.WellFormed 10 (addHypLoopForJ n i j tLo scale rem off tr) ∧
        IntTrie.evalTrie (mValForJ f (max i j)) 1 0
            (addHypLoopForJ n i j tLo scale rem off tr) =
          IntTrie.evalTrie (mValForJ f (max i j)) 1 0 tr +
            (scale : ℝ) *
              ∑ m ∈ Finset.range rem,
                (Nat.choose i (tLo + (off + m)) *
                  Nat.choose (n - i) (j - (tLo + (off + m))) : ℝ) *
                  pairCorr f i j (tLo + (off + m))
  | 0, _, tr, _, hwf => by simp [addHypLoopForJ, hwf]
  | rem + 1, off, tr, hlt, hwf => by
    simp only [addHypLoopForJ]
    set tv := tLo + off
    have hkey_lt : min i j + 32 * tv < 2 ^ 10 := by omega
    have hvalid : ValidTriple n i j tv := ⟨hi, hj, by omega, by omega, by omega⟩
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_addAt (mValForJ f (max i j)) 10
      (min i j + 32 * tv) 1 0 (scale * ((fastChoose i tv * fastChoose (n - i) (j - tv) : ℕ) : ℤ))
      tr hkey_lt hwf
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addHypLoopForJ f hn i j tLo scale hi hj htLo
      rem (off + 1) _ (by omega) hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1, Finset.sum_range_succ']
    have hshift :
        ∑ m ∈ Finset.range rem,
          (Nat.choose i (tLo + (off + 1 + m)) *
            Nat.choose (n - i) (j - (tLo + (off + 1 + m))) : ℝ) *
            pairCorr f i j (tLo + (off + 1 + m)) =
        ∑ m ∈ Finset.range rem,
          (Nat.choose i (tLo + (off + (m + 1))) *
            Nat.choose (n - i) (j - (tLo + (off + (m + 1)))) : ℝ) *
            pairCorr f i j (tLo + (off + (m + 1))) := by
      apply Finset.sum_congr rfl; intro m _
      have : off + 1 + m = off + (m + 1) := by omega
      rw [this]
    rw [hshift]
    simp only [zero_add, one_mul, Nat.add_zero, fastChoose_eq, mValForJ_key f hn hvalid]
    push_cast; ring

private lemma addMListForJ_wf_and_sum {n : ℕ} (f : BooleanFun n) (hn : n < 32) (scale : ℤ) :
    ∀ (l : List (ℕ × ℕ × ℕ × ℤ)) (tM : ℕ → IntTrie),
      (∀ q ∈ l, ValidTriple n q.1 q.2.1 q.2.2.1) →
      (∀ j ≤ n, IntTrie.WellFormed 10 (tM j)) →
      (∀ j ≤ n, IntTrie.WellFormed 10 (addMListForJ j scale l (tM j))) ∧
        ∑ j ∈ Finset.range (n + 1),
          IntTrie.evalTrie (mValForJ f j) 1 0 (addMListForJ j scale l (tM j)) =
        (∑ j ∈ Finset.range (n + 1), IntTrie.evalTrie (mValForJ f j) 1 0 (tM j)) +
          (scale : ℝ) * evalTargetM f l
  | [], tM, _, hwf => ⟨hwf, by simp [addMListForJ, evalTargetM]⟩
  | (i, j, tv, c) :: rest, tM, hall, hwf => by
    have hhd : ValidTriple n i j tv := hall (i, j, tv, c) (List.mem_cons_self ..)
    have htl : ∀ q ∈ rest, ValidTriple n q.1 q.2.1 q.2.2.1 :=
      fun q hq => hall q (List.mem_cons_of_mem _ hq)
    have hkey_lt : min i j + 32 * tv < 2 ^ 10 := by
      obtain ⟨hi, hj, hti, _, _⟩ := hhd; omega
    have hmax_le : max i j ≤ n := max_le hhd.1 hhd.2.1
    let tM' : ℕ → IntTrie := fun k =>
      if max i j == k then IntTrie.addAt 10 (min i j + 32 * tv) (scale * c) (tM k) else tM k
    have hwf' : ∀ k ≤ n, IntTrie.WellFormed 10 (tM' k) := by
      intro k hk
      dsimp only [tM']
      split_ifs
      · exact (IntTrie.wellFormed_and_eval_addAt (mValForJ f k) 10
          (min i j + 32 * tv) 1 0 (scale * c) (tM k) hkey_lt (hwf k hk)).1
      · exact hwf k hk
    obtain ⟨hwfR, hsumR⟩ := addMListForJ_wf_and_sum f hn scale rest tM' htl hwf'
    refine ⟨hwfR, ?_⟩
    dsimp only [addMListForJ, evalTargetM]
    rw [hsumR]
    have hstep :
        ∑ k ∈ Finset.range (n + 1), IntTrie.evalTrie (mValForJ f k) 1 0 (tM' k) =
        (∑ k ∈ Finset.range (n + 1), IntTrie.evalTrie (mValForJ f k) 1 0 (tM k)) +
          (scale : ℝ) * ((c : ℝ) * pairCorr f i j tv) := by
      have hterm : ∀ k ∈ Finset.range (n + 1),
          IntTrie.evalTrie (mValForJ f k) 1 0 (tM' k) =
          IntTrie.evalTrie (mValForJ f k) 1 0 (tM k) +
            (if max i j = k then (scale : ℝ) * ((c : ℝ) * pairCorr f i j tv) else 0) := by
        intro k hk
        have hkn : k ≤ n := by rw [Finset.mem_range] at hk; omega
        dsimp only [tM']
        by_cases heq : max i j = k
        · subst heq
          simp only [beq_self_eq_true, ↓reduceIte]
          obtain ⟨_, hev⟩ := IntTrie.wellFormed_and_eval_addAt (mValForJ f (max i j)) 10
            (min i j + 32 * tv) 1 0 (scale * c) (tM (max i j)) hkey_lt (hwf (max i j) hkn)
          rw [hev]; simp only [zero_add, one_mul, mValForJ_key f hn hhd]
          push_cast; ring
        · have hbf : (max i j == k) = false := by simp [heq]
          simp [hbf, heq]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single (max i j)]
      · simp
      · intro k _ hne; simp [hne.symm]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
    rw [hstep]; ring

private lemma psdPairTrieForJ_wf_and_sum {n : ℕ} (f : BooleanFun n)
    (hn : n < 32) (k r c : ℕ) (scaleRC : ℤ)
    (hkn : 2 * k ≤ n) (hr : r ≤ n - 2 * k) (hc : c ≤ n - 2 * k) :
    (∀ j ≤ n, IntTrie.WellFormed 10 (psdPairTrieForJ n k j r c scaleRC)) ∧
      ∑ j ∈ Finset.Icc k (n - k),
        IntTrie.evalTrie (mValForJ f j) 1 0 (psdPairTrieForJ n k j r c scaleRC) =
        (scaleRC : ℝ) * bTilde k (fun x => boolToReal (f x)) r c := by
  set r' := min r c
  set c' := max r c
  have hr' : r' ≤ n - 2 * k := min_le_of_left_le hr
  have hc' : c' ≤ n - 2 * k := max_le hr hc
  have hbase_mem : k + c' ∈ Finset.Icc k (n - k) := by rw [Finset.mem_Icc]; omega
  by_cases hs : scaleRC = 0
  · subst hs
    refine ⟨fun j _ => by simp [psdPairTrieForJ, IntTrie.wellFormed_empty], ?_⟩
    simp [psdPairTrieForJ, IntTrie.evalTrie]
  · have hbeq0 : (scaleRC == 0) = false := by simp [hs]
    set n2k := n - 2 * k
    set bLo := r' + c' - n2k
    set bHi := min r' c'
    have hkr'_lt : k + r' < 2 ^ 5 := by omega
    have hsum_b : (scaleRC : ℝ) *
        ∑ m ∈ Finset.range (bHi - bLo + 1),
          (pairCount n2k r' c' (bLo + (0 + m)) : ℝ) *
            ∑ a ∈ Finset.range (k + 1),
              (((-1 : ℤ) ^ (k - a) * (Nat.choose k a : ℤ) : ℤ) : ℝ) *
                pairCorr f (k + r') (k + c') (a + (bLo + (0 + m))) =
        (scaleRC : ℝ) * bTilde k (fun x => boolToReal (f x)) r' c' := by
      congr 1
      unfold bTilde
      apply Finset.sum_nbij (fun m => bLo + m)
      · intro m hm; rw [Finset.mem_range] at hm; rw [Finset.mem_Icc]; omega
      · intro m₁ _ m₂ _ hEq; dsimp only at hEq; omega
      · intro b hb; rw [Finset.mem_coe, Finset.mem_Icc] at hb
        refine ⟨b - bLo, ?_, by dsimp only; omega⟩
        rw [Finset.mem_coe, Finset.mem_range]; omega
      · intro _ _; simp only [n2k, zero_add, pairCorrR_bool]
    have hb_eq : bTilde k (fun x => boolToReal (f x)) r' c' =
        bTilde k (fun x => boolToReal (f x)) r c := by
      by_cases hrc : r ≤ c
      · simp [r', c', min_eq_left hrc, max_eq_right hrc]
      · have hcr : c ≤ r := by omega
        simp only [r', c', min_eq_right hcr, max_eq_left hcr]
        exact bTilde_comm f k c r hkn hc hr
    have hmod := IntTrie.wellFormed_and_eval_modifyAt (mValForJ f (k + c')) 5 5
      (k + r') 1 0
      ((scaleRC : ℝ) * bTilde k (fun x => boolToReal (f x)) r' c')
      (psdBLoop5 n2k k r' c' bLo (scaleRC * (fastChoose n2k r' : ℤ)) (bHi - bLo + 1) 0)
      .empty hkr'_lt (IntTrie.wellFormed_empty 10) (by
        intro s hs'
        have hval_j : ∀ t, ValidTriple n (k + r') (k + c') t →
            mValForJ f (k + c') ((k + r') + 32 * t) = pairCorr f (k + r') (k + c') t := by
          intro t _
          have h1 : ((k + r') + 32 * t) % 32 = k + r' := by omega
          have h2 : ((k + r') + 32 * t) / 32 = t := by omega
          simp only [mValForJ, h1, h2]
        obtain ⟨hwfB, hevB⟩ := wellFormed_and_eval_psdBLoop5 f (mValForJ f (k + c')) 32
          (k + r') hn k r' c' bLo scaleRC
          hkn hr' hc' (le_refl _) hval_j (bHi - bLo + 1) 0 s (by omega) hs'
        refine ⟨hwfB, ?_⟩
        simp only [zero_add, one_mul, mul_one]
        have hpow : (2 ^ 5 : ℕ) = 32 := by decide
        rw [hpow, hevB, hsum_b])
    refine ⟨?_, ?_⟩
    · intro j _
      unfold psdPairTrieForJ
      by_cases hj : k + max r c = j
      · rw [hbeq0, hj]; simp only [beq_self_eq_true, Bool.not_true, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte]
        exact hmod.1
      · have hbf : (k + max r c == j) = false := by simp [hj]
        rw [hbeq0, hbf]; exact IntTrie.wellFormed_empty 10
    · rw [Finset.sum_eq_single (k + c')]
      · unfold psdPairTrieForJ
        rw [hbeq0]
        simp only [c', beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        rw [hmod.2, hb_eq]; simp [IntTrie.evalTrie]
      · intro j _ hne
        have hne' : k + max r c ≠ j := hne.symm
        have hbf : (k + max r c == j) = false := by simp [hne']
        unfold psdPairTrieForJ
        rw [hbeq0, hbf]; simp [IntTrie.evalTrie]
      · intro hnot; exact absurd hbase_mem hnot

private lemma psdUpperInnerForJ_wf_and_sum {n : ℕ} (f : BooleanFun n)
    (hn : n < 32) (k r : ℕ) (wr : ℤ) (hkn : 2 * k ≤ n) (hr : r ≤ n - 2 * k) :
    ∀ l, (∀ q ∈ l, q.1 ≤ n - 2 * k) →
      (∀ j ≤ n, IntTrie.WellFormed 10 (psdUpperInnerForJ n k j r wr l)) ∧
        ∑ j ∈ Finset.Icc k (n - k),
          IntTrie.evalTrie (mValForJ f j) 1 0 (psdUpperInnerForJ n k j r wr l) =
          (l.map (fun q => 2 * (wr : ℝ) * (q.2 : ℝ) *
            bTilde k (fun x => boolToReal (f x)) r q.1)).sum
  | [], _ => ⟨fun _ _ => IntTrie.wellFormed_empty 10, by simp [psdUpperInnerForJ, IntTrie.evalTrie]⟩
  | (c, wc) :: tl, hall => by
    have hc : c ≤ n - 2 * k := hall (c, wc) (List.mem_cons_self ..)
    obtain ⟨hwf1, hev1⟩ := psdPairTrieForJ_wf_and_sum f hn k r c (2 * wr * wc) hkn hr hc
    obtain ⟨hwf2, hev2⟩ := psdUpperInnerForJ_wf_and_sum f hn k r wr hkn hr tl
      (fun q hq => hall q (List.mem_cons_of_mem _ hq))
    refine ⟨fun j hj => (IntTrie.wellFormed_and_eval_merge (mValForJ f j) 10 1 0 _ _
      (hwf1 j hj) (hwf2 j hj)).1, ?_⟩
    simp only [psdUpperInnerForJ, List.map_cons, List.sum_cons]
    have hsplit : ∑ j ∈ Finset.Icc k (n - k),
        IntTrie.evalTrie (mValForJ f j) 1 0
          (IntTrie.merge (psdPairTrieForJ n k j r c (2 * wr * wc))
            (psdUpperInnerForJ n k j r wr tl)) =
      (∑ j ∈ Finset.Icc k (n - k),
        IntTrie.evalTrie (mValForJ f j) 1 0 (psdPairTrieForJ n k j r c (2 * wr * wc))) +
      (∑ j ∈ Finset.Icc k (n - k),
        IntTrie.evalTrie (mValForJ f j) 1 0 (psdUpperInnerForJ n k j r wr tl)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j hj
      have hjn : j ≤ n := by rw [Finset.mem_Icc] at hj; omega
      exact (IntTrie.wellFormed_and_eval_merge (mValForJ f j) 10 1 0 _ _
        (hwf1 j hjn) (hwf2 j hjn)).2
    rw [hsplit, hev1, hev2]; push_cast; ring

private lemma psdUpperTrieForJ_wf_and_sum {n : ℕ} (f : BooleanFun n)
    (hn : n < 32) (k : ℕ) (hkn : 2 * k ≤ n) :
    ∀ w, (∀ p ∈ w, p.1 ≤ n - 2 * k) →
      (∀ j ≤ n, IntTrie.WellFormed 10 (psdUpperTrieForJ n k j w)) ∧
        ∑ j ∈ Finset.Icc k (n - k),
          IntTrie.evalTrie (mValForJ f j) 1 0 (psdUpperTrieForJ n k j w) = evalPsdList k f w
  | [], _ => ⟨fun _ _ => IntTrie.wellFormed_empty 10, by
      simp [psdUpperTrieForJ, evalPsdList, IntTrie.evalTrie]⟩
  | (r, wr) :: tl, hall => by
    have hr : r ≤ n - 2 * k := hall (r, wr) (List.mem_cons_self ..)
    have htl : ∀ q ∈ tl, q.1 ≤ n - 2 * k := fun q hq => hall q (List.mem_cons_of_mem _ hq)
    obtain ⟨hwfD, hevD⟩ := psdPairTrieForJ_wf_and_sum f hn k r r (wr * wr) hkn hr hr
    obtain ⟨hwfI, hevI⟩ := psdUpperInnerForJ_wf_and_sum f hn k r wr hkn hr tl htl
    obtain ⟨hwfT, hevT⟩ := psdUpperTrieForJ_wf_and_sum f hn k hkn tl htl
    have hwfM1 : ∀ j ≤ n, IntTrie.WellFormed 10
        (IntTrie.merge (psdPairTrieForJ n k j r r (wr * wr))
          (psdUpperInnerForJ n k j r wr tl)) :=
      fun j hj => (IntTrie.wellFormed_and_eval_merge (mValForJ f j) 10 1 0 _ _
        (hwfD j hj) (hwfI j hj)).1
    refine ⟨fun j hj => (IntTrie.wellFormed_and_eval_merge (mValForJ f j) 10 1 0 _ _
      (hwfM1 j hj) (hwfT j hj)).1, ?_⟩
    have hsplit : ∑ j ∈ Finset.Icc k (n - k),
        IntTrie.evalTrie (mValForJ f j) 1 0 (psdUpperTrieForJ n k j ((r, wr) :: tl)) =
      (∑ j ∈ Finset.Icc k (n - k),
        IntTrie.evalTrie (mValForJ f j) 1 0 (psdPairTrieForJ n k j r r (wr * wr))) +
      (∑ j ∈ Finset.Icc k (n - k),
        IntTrie.evalTrie (mValForJ f j) 1 0 (psdUpperInnerForJ n k j r wr tl)) +
      (∑ j ∈ Finset.Icc k (n - k),
        IntTrie.evalTrie (mValForJ f j) 1 0 (psdUpperTrieForJ n k j tl)) := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j hj
      have hjn : j ≤ n := by rw [Finset.mem_Icc] at hj; omega
      dsimp only [psdUpperTrieForJ]
      rw [(IntTrie.wellFormed_and_eval_merge (mValForJ f j) 10 1 0 _ _ (hwfM1 j hjn) (hwfT j hjn)).2,
        (IntTrie.wellFormed_and_eval_merge (mValForJ f j) 10 1 0 _ _ (hwfD j hjn) (hwfI j hjn)).2]
    rw [hsplit, hevD, hevI, hevT]
    -- Match `wellFormed_and_eval_psdUpperTrie` algebra via `evalPsdList`:
    obtain ⟨_, hevFull⟩ := wellFormed_and_eval_psdUpperTrie f hn k hkn ((r, wr) :: tl) hall
    obtain ⟨hwfDF, hevDF⟩ := wellFormed_and_eval_psdPairTrie f hn k r r (wr * wr) hkn hr hr
    obtain ⟨hwfIF, hevIF⟩ := wellFormed_and_eval_psdUpperInner f hn k r wr hkn hr tl htl
    obtain ⟨hwfTF, hevTF⟩ := wellFormed_and_eval_psdUpperTrie f hn k hkn tl htl
    obtain ⟨hwfMF1, hevMF1⟩ := IntTrie.wellFormed_and_eval_merge (terwMVal f) 15 1 0 _ _ hwfDF hwfIF
    obtain ⟨_, hevMF2⟩ := IntTrie.wellFormed_and_eval_merge (terwMVal f) 15 1 0 _ _ hwfMF1 hwfTF
    dsimp only [psdUpperTrie] at hevFull
    rw [hevMF2, hevMF1, hevDF, hevIF, hevTF] at hevFull
    exact hevFull

private lemma expandMTrieForJ_sound {n d : ℕ} (f : BooleanFun n)
    (hd : d < 16) (jTarget : ℕ) (hjTarget : jTarget ≤ n)
    (c : ℕ → ℕ → ℕ → ℝ)
    (hc : ∀ j ≤ n, ∀ a b, a ≤ j → b ≤ n - j →
      pairCorr f (a + b) j a =
        ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ)) :
    let cValJ : ℕ → ℝ := fun idx => c jTarget (idx % 16) (idx / 16)
    ∀ (t : IntTrie) (step base : ℕ),
      (expandMTrieForJ n d jTarget step base t).1 = true →
      IntTrie.WellFormed 8 (expandMTrieForJ n d jTarget step base t).2 ∧
        IntTrie.evalTrie cValJ 1 0 (expandMTrieForJ n d jTarget step base t).2 =
          IntTrie.evalTrie (mValForJ f jTarget) step base t := by
  intro cValJ t
  induction t with
  | empty =>
    intro step base _
    exact ⟨trivial, by simp [expandMTrieForJ, IntTrie.evalTrie]⟩
  | leaf v =>
    intro step base hok
    simp only [expandMTrieForJ] at hok ⊢
    by_cases hv : v = 0
    · subst hv; exact ⟨IntTrie.wellFormed_empty 8, by simp [IntTrie.evalTrie]⟩
    · have hbeq : (v == 0) = false := by simp [hv]
      rw [hbeq] at hok ⊢; simp only [Bool.false_eq_true, ↓reduceIte] at hok ⊢
      split_ifs at hok ⊢ with hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨_, hvt⟩ := hcond
      have hvalid := (validTripleB_iff n (base % 32) jTarget (base / 32)).mp hvt
      obtain ⟨_, hjn, hti, htj, hij_n⟩ := hvalid
      obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalHJ c n d jTarget (base / 32)
        (base % 32 - base / 32) v .empty hd htj (by omega) trivial
      refine ⟨hwfC, ?_⟩
      dsimp only
      rw [hevC]; simp only [IntTrie.evalTrie, zero_add]
      have hcorr : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c jTarget r s * (Nat.choose (base / 32) r : ℝ) *
            (Nat.choose (base % 32 - base / 32) s : ℝ) = mValForJ f jTarget base := by
        rw [← hc jTarget hjTarget (base / 32) (base % 32 - base / 32) htj (by omega),
          Nat.add_sub_of_le hti]
        rfl
      rw [hcorr]
  | node lo hi ihlo ihhi =>
    intro step base hok
    simp only [expandMTrieForJ, Bool.and_eq_true] at hok ⊢
    obtain ⟨hwf1, hev1⟩ := ihlo (2 * step) base hok.1
    obtain ⟨hwf2, hev2⟩ := ihhi (2 * step) (base + step) hok.2
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_merge cValJ 8 1 0 _ _ hwf1 hwf2
    refine ⟨hwfM, ?_⟩
    rw [hevM, hev1, hev2]; simp [IntTrie.evalTrie]

private lemma psdStepForJ_wf_and_sum {n d : ℕ} (f : BooleanFun n)
    (c : ℕ → ℕ → ℕ → ℝ) (hn : n < 32) (hd : d < 16)
    (step : PsdBinoStep) (hok : psdStepOk n step = true) :
    let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
    let cValJ : ℕ → ℕ → ℝ := fun j idx => c j (idx % 16) (idx / 16)
    (∀ j ≤ n, IntTrie.WellFormed 8 (psdStepCForJ n d j step)) ∧
      (∀ j ≤ n, IntTrie.WellFormed 10 (psdStepMForJ n j step)) ∧
      IntTrie.evalTrie cVal 1 0 (psdStepC n d step) +
        IntTrie.evalTrie (terwMVal f) 1 0 (psdStepM n step) =
        ∑ j ∈ Finset.range (n + 1),
          (IntTrie.evalTrie (cValJ j) 1 0 (psdStepCForJ n d j step) +
           IntTrie.evalTrie (mValForJ f j) 1 0 (psdStepMForJ n j step)) := by
  intro cVal cValJ
  have hsingleM : ∀ (i j t : ℕ) (sc : ℤ), ValidTriple n i j t →
      (∀ k ≤ n, IntTrie.WellFormed 10
        (if max i j == k then IntTrie.addAt 10 (min i j + 32 * t) sc .empty else .empty)) ∧
      IntTrie.evalTrie (terwMVal f) 1 0 (IntTrie.addAt 15 (canonMKey i j t) sc .empty) =
        ∑ k ∈ Finset.range (n + 1),
          IntTrie.evalTrie (mValForJ f k) 1 0
            (if max i j == k then IntTrie.addAt 10 (min i j + 32 * t) sc .empty else .empty) := by
    intro i j t sc hv
    have ⟨hi, hj, hti, htj, _⟩ := hv
    have hkey10 : min i j + 32 * t < 2 ^ 10 := by omega
    have hkey15 : canonMKey i j t < 2 ^ 15 := canonMKey_lt i j t (by omega) (by omega) (by omega)
    obtain ⟨_, hev15⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t)
      1 0 sc .empty hkey15 trivial
    refine ⟨?_, ?_⟩
    · intro k _
      split_ifs
      · exact (IntTrie.wellFormed_and_eval_addAt (mValForJ f k) 10
          (min i j + 32 * t) 1 0 sc .empty hkey10 trivial).1
      · exact IntTrie.wellFormed_empty 10
    · rw [Finset.sum_eq_single (max i j)]
      · simp only [beq_self_eq_true, ↓reduceIte]
        obtain ⟨_, hev10⟩ := IntTrie.wellFormed_and_eval_addAt (mValForJ f (max i j)) 10
          (min i j + 32 * t) 1 0 sc .empty hkey10 trivial
        rw [hev15, hev10]
        simp only [IntTrie.evalTrie, zero_add, one_mul, terwMVal_canonMKey f hn hv,
          mValForJ_key f hn hv]
      · intro k _ hne
        have hbf : (max i j == k) = false := by simp [hne.symm]
        simp [hbf, IntTrie.evalTrie]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
  cases step with
  | eqSym i j t μ =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    obtain ⟨hin, hjn, hti, htj, hij⟩ := hvalid
    obtain ⟨hwfH1, hevH1⟩ := wellFormed_and_eval_addEvalH c n d j t (i - t) μ .empty (by omega) hd hjn htj (by omega) trivial
    obtain ⟨_, hevH2⟩ := wellFormed_and_eval_addEvalH c n d i t (j - t) (-μ) _ (by omega) hd hin hti (by omega) hwfH1
    obtain ⟨hwfJ1, hevJ1⟩ := wellFormed_and_eval_addEvalHJ c n d j t (i - t) μ .empty hd htj (by omega) trivial
    obtain ⟨hwfJ2, hevJ2⟩ := wellFormed_and_eval_addEvalHJ c n d i t (j - t) (-μ) .empty hd hti (by omega) trivial
    have hwf1 : ∀ k ≤ n, IntTrie.WellFormed 8 (if j == k then addEvalHJ n d j t (i - t) μ .empty else .empty) := by
      intro k _; split_ifs; exact hwfJ1; exact trivial
    have hwf2 : ∀ k ≤ n, IntTrie.WellFormed 8 (if i == k then addEvalHJ n d i t (j - t) (-μ) .empty else .empty) := by
      intro k _; split_ifs; exact hwfJ2; exact trivial
    refine ⟨fun k hk => (IntTrie.wellFormed_and_eval_merge (cValJ k) 8 1 0 _ _ (hwf1 k hk) (hwf2 k hk)).1,
      fun _ _ => IntTrie.wellFormed_empty 10, ?_⟩
    dsimp only [psdStepC, psdStepM, psdStepCForJ, psdStepMForJ]
    simp only [IntTrie.evalTrie, add_zero]
    have hmerge : ∑ k ∈ Finset.range (n + 1),
        IntTrie.evalTrie (cValJ k) 1 0
          (IntTrie.merge (if j == k then addEvalHJ n d j t (i - t) μ .empty else .empty)
                         (if i == k then addEvalHJ n d i t (j - t) (-μ) .empty else .empty)) =
      (∑ k ∈ Finset.range (n + 1),
        IntTrie.evalTrie (cValJ k) 1 0 (if j == k then addEvalHJ n d j t (i - t) μ .empty else .empty)) +
      (∑ k ∈ Finset.range (n + 1),
        IntTrie.evalTrie (cValJ k) 1 0 (if i == k then addEvalHJ n d i t (j - t) (-μ) .empty else .empty)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k hk
      have hkn : k ≤ n := by rw [Finset.mem_range] at hk; omega
      exact (IntTrie.wellFormed_and_eval_merge (cValJ k) 8 1 0 _ _ (hwf1 k hkn) (hwf2 k hkn)).2
    rw [hmerge]
    have hs1 : ∑ k ∈ Finset.range (n + 1),
        IntTrie.evalTrie (cValJ k) 1 0 (if j == k then addEvalHJ n d j t (i - t) μ .empty else .empty) =
        IntTrie.evalTrie (cValJ j) 1 0 (addEvalHJ n d j t (i - t) μ .empty) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hne
        have hbf : (j == k) = false := by simp [hne.symm]
        simp [hbf, IntTrie.evalTrie]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
    have hs2 : ∑ k ∈ Finset.range (n + 1),
        IntTrie.evalTrie (cValJ k) 1 0 (if i == k then addEvalHJ n d i t (j - t) (-μ) .empty else .empty) =
        IntTrie.evalTrie (cValJ i) 1 0 (addEvalHJ n d i t (j - t) (-μ) .empty) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hne
        have hbf : (i == k) = false := by simp [hne.symm]
        simp [hbf, IntTrie.evalTrie]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
    rw [hs1, hs2, hevH2, hevH1, hevJ1, hevJ2]
    simp [IntTrie.evalTrie]
  | eqDiag i μ =>
    simp only [psdStepOk, decide_eq_true_eq] at hok
    have hv : ValidTriple n i i i := ⟨hok, hok, le_refl i, le_refl i, by omega⟩
    obtain ⟨hwfM, hsumM⟩ := hsingleM i i i (μ * (fastChoose n i : ℤ)) hv
    simp only [max_self, min_self] at hwfM hsumM
    refine ⟨fun _ _ => trivial, hwfM, ?_⟩
    dsimp only [psdStepC, psdStepM, psdStepCForJ, psdStepMForJ]
    simp only [IntTrie.evalTrie, zero_add]
    exact hsumM
  | eqHyp i j μ =>
    simp only [psdStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hin, hjn⟩ := hok
    set tLo := i + j - n
    set tHi := min i j
    have hmax_le : max i j ≤ n := max_le hin hjn
    obtain ⟨_, hev15⟩ := wellFormed_and_eval_addHypLoop f hn i j tLo (μ * (fastChoose n i : ℤ))
      hin hjn (le_refl _) (tHi - tLo + 1) 0 .empty (by omega) trivial
    obtain ⟨hwf10, hev10⟩ := wellFormed_and_eval_addHypLoopForJ f hn i j tLo (μ * (fastChoose n i : ℤ))
      hin hjn (le_refl _) (tHi - tLo + 1) 0 .empty (by omega) trivial
    refine ⟨fun _ _ => trivial, ?_, ?_⟩
    · intro k _; dsimp only [psdStepMForJ]; split_ifs; exact hwf10; exact IntTrie.wellFormed_empty 10
    · dsimp only [psdStepC, psdStepM, psdStepCForJ, psdStepMForJ]
      simp only [IntTrie.evalTrie, zero_add]
      rw [Finset.sum_eq_single (max i j)]
      · simp only [beq_self_eq_true, ↓reduceIte]
        rw [hev15, hev10]; simp [IntTrie.evalTrie]
      · intro k _ hne
        have hbf : (max i j == k) = false := by simp [hne.symm]
        simp [hbf, IntTrie.evalTrie]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
  | ubMLo0 i j t lam =>
    have hv := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfM, hsumM⟩ := hsingleM i j t (lam : ℤ) hv
    refine ⟨fun _ _ => trivial, hwfM, ?_⟩
    dsimp only [psdStepC, psdStepM, psdStepCForJ, psdStepMForJ]
    simp only [IntTrie.evalTrie, zero_add]; exact hsumM
  | ubMMcc i j t lam =>
    have hv := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfM, hsumM⟩ := hsingleM i j t ((lam : ℤ) * ((fastChoose n i : ℤ) * (fastChoose n j : ℤ))) hv
    refine ⟨fun _ _ => trivial, hwfM, ?_⟩
    dsimp only [psdStepC, psdStepM, psdStepCForJ, psdStepMForJ]
    simp only [IntTrie.evalTrie, zero_add]; exact hsumM
  | ubMLePi i j t lam =>
    have hv := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfM, hsumM⟩ := hsingleM i j t (-(lam : ℤ) * (fastChoose n i : ℤ)) hv
    refine ⟨fun _ _ => trivial, hwfM, ?_⟩
    dsimp only [psdStepC, psdStepM, psdStepCForJ, psdStepMForJ]
    simp only [IntTrie.evalTrie, zero_add]; exact hsumM
  | ubMLePj i j t lam =>
    have hv := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfM, hsumM⟩ := hsingleM i j t (-(lam : ℤ) * (fastChoose n j : ℤ)) hv
    refine ⟨fun _ _ => trivial, hwfM, ?_⟩
    dsimp only [psdStepC, psdStepM, psdStepCForJ, psdStepMForJ]
    simp only [IntTrie.evalTrie, zero_add]; exact hsumM
  | ubPsd k w lam =>
    simp only [psdStepOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
    obtain ⟨hkn, hw⟩ := hok
    have hw' : ∀ p ∈ w, p.1 ≤ n - 2 * k := fun p hp => by simpa using hw p hp
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_psdUpperTrie f hn k hkn w hw'
    obtain ⟨_, hevScaleFull⟩ := wellFormed_and_eval_scaleTrie (terwMVal f) 15 (lam : ℤ) 1 0 _ hwfU
    obtain ⟨hwfJ, hsumJ⟩ := psdUpperTrieForJ_wf_and_sum f hn k hkn w hw'
    refine ⟨fun _ _ => trivial, ?_, ?_⟩
    · intro j hj; dsimp only [psdStepMForJ]
      split_ifs
      · exact (wellFormed_and_eval_scaleTrie (mValForJ f j) 10 (lam : ℤ) 1 0 _ (hwfJ j hj)).1
      · exact IntTrie.wellFormed_empty 10
    · dsimp only [psdStepC, psdStepM, psdStepCForJ, psdStepMForJ]
      simp only [IntTrie.evalTrie, zero_add]
      rw [hevScaleFull, hevU]
      have hsub : Finset.Icc k (n - k) ⊆ Finset.range (n + 1) := by
        intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
      rw [← Finset.sum_subset hsub]
      · have hcongr : ∑ j ∈ Finset.Icc k (n - k),
            IntTrie.evalTrie (mValForJ f j) 1 0
              (if decide (k ≤ j) && decide (j ≤ n - k) then
                scaleTrie (lam : ℤ) (psdUpperTrieForJ n k j w) else .empty) =
            ∑ j ∈ Finset.Icc k (n - k),
              ((lam : ℤ) : ℝ) * IntTrie.evalTrie (mValForJ f j) 1 0 (psdUpperTrieForJ n k j w) := by
          apply Finset.sum_congr rfl; intro j hj
          have hjn : j ≤ n := by rw [Finset.mem_Icc] at hj; omega
          have hbt : (decide (k ≤ j) && decide (j ≤ n - k)) = true := by
            rw [Finset.mem_Icc] at hj; simp [hj.1, hj.2]
          rw [hbt]; simp only [↓reduceIte]
          exact (wellFormed_and_eval_scaleTrie (mValForJ f j) 10 (lam : ℤ) 1 0 _ (hwfJ j hjn)).2
        rw [hcongr, ← Finset.mul_sum, hsumJ]
      · intro j _ hnot
        rw [Finset.mem_Icc] at hnot
        have hbf : (decide (k ≤ j) && decide (j ≤ n - k)) = false := by
          by_cases hk1 : k ≤ j
          · by_cases hk2 : j ≤ n - k
            · exact absurd ⟨hk1, hk2⟩ hnot
            · simp [hk2]
          · simp [hk1]
        simp [hbf, IntTrie.evalTrie]

private lemma psdTreeForJ_wf_and_sum {n d : ℕ} (f : BooleanFun n)
    (c : ℕ → ℕ → ℕ → ℝ) (hn : n < 32) (hd : d < 16) :
    let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
    let cValJ : ℕ → ℕ → ℝ := fun j idx => c j (idx % 16) (idx / 16)
    ∀ (tree : BinTree PsdBinoStep), tree.all (psdStepOk n) = true →
      (∀ j ≤ n, IntTrie.WellFormed 8 (IntTrie.mergeTree (psdStepCForJ n d j) tree)) ∧
      (∀ j ≤ n, IntTrie.WellFormed 10 (IntTrie.mergeTree (psdStepMForJ n j) tree)) ∧
      IntTrie.WellFormed 14 (IntTrie.mergeTree (psdStepC n d) tree) ∧
      IntTrie.WellFormed 15 (IntTrie.mergeTree (psdStepM n) tree) ∧
      IntTrie.evalTrie cVal 1 0 (IntTrie.mergeTree (psdStepC n d) tree) +
        IntTrie.evalTrie (terwMVal f) 1 0 (IntTrie.mergeTree (psdStepM n) tree) =
        ∑ j ∈ Finset.range (n + 1),
          (IntTrie.evalTrie (cValJ j) 1 0 (IntTrie.mergeTree (psdStepCForJ n d j) tree) +
           IntTrie.evalTrie (mValForJ f j) 1 0 (IntTrie.mergeTree (psdStepMForJ n j) tree)) := by
  intro cVal cValJ tree
  induction tree with
  | empty =>
    intro _
    exact ⟨fun _ _ => trivial, fun _ _ => IntTrie.wellFormed_empty 10, trivial,
      IntTrie.wellFormed_empty 15, by simp [IntTrie.mergeTree, IntTrie.evalTrie]⟩
  | leaf s =>
    intro hok
    dsimp only [BinTree.all] at hok
    obtain ⟨hwfCJ, hwfMJ, hsum⟩ := psdStepForJ_wf_and_sum f c hn hd s hok
    have hwfCM : IntTrie.WellFormed 14 (psdStepC n d s) ∧ IntTrie.WellFormed 15 (psdStepM n s) := by
      cases s with
      | eqSym i j t μ =>
        have hv := (validTripleB_iff n i j t).mp hok
        obtain ⟨hin, hjn, hti, htj, hij⟩ := hv
        have h1 := (wellFormed_and_eval_addEvalH c n d j t (i - t) μ .empty (by omega) hd hjn htj (by omega) trivial).1
        have h2 := (wellFormed_and_eval_addEvalH c n d i t (j - t) (-μ) _ (by omega) hd hin hti (by omega) h1).1
        exact ⟨h2, IntTrie.wellFormed_empty 15⟩
      | eqDiag i μ =>
        simp only [psdStepOk, decide_eq_true_eq] at hok
        exact ⟨trivial, (IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i i i)
          1 0 _ .empty (canonMKey_lt _ _ _ (by omega) (by omega) (by omega)) trivial).1⟩
      | eqHyp i j μ =>
        simp only [psdStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        exact ⟨trivial, (wellFormed_and_eval_addHypLoop f hn i j (i + j - n)
          (μ * (fastChoose n i : ℤ)) hok.1 hok.2 (le_refl _) (min i j - (i + j - n) + 1) 0 .empty
          (by omega) trivial).1⟩
      | ubMLo0 i j t lam | ubMMcc i j t lam | ubMLePi i j t lam | ubMLePj i j t lam =>
        have hv := (validTripleB_iff n i j t).mp hok
        exact ⟨trivial, (IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t)
          1 0 _ .empty (canonMKey_lt _ _ _ (by have := hv.1; omega)
            (by have := hv.2.1; omega) (by have := hv.1; have := hv.2.2.1; omega)) trivial).1⟩
      | ubPsd k w lam =>
        simp only [psdStepOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
        have hw' : ∀ p ∈ w, p.1 ≤ n - 2 * k := fun p hp => by simpa using hok.2 p hp
        have h1 := (wellFormed_and_eval_psdUpperTrie f hn k hok.1 w hw').1
        exact ⟨trivial, (wellFormed_and_eval_scaleTrie (terwMVal f) 15 (lam : ℤ) 1 0 _ h1).1⟩
    exact ⟨hwfCJ, hwfMJ, hwfCM.1, hwfCM.2, hsum⟩
  | node l r ihl ihr =>
    intro hok
    simp only [BinTree.all, Bool.and_eq_true] at hok
    obtain ⟨hwfCJl, hwfMJl, hwfCl, hwfMl, hsuml⟩ := ihl hok.1
    obtain ⟨hwfCJr, hwfMJr, hwfCr, hwfMr, hsumr⟩ := ihr hok.2
    obtain ⟨hwfC, hevC⟩ := IntTrie.wellFormed_and_eval_merge cVal 14 1 0 _ _ hwfCl hwfCr
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_merge (terwMVal f) 15 1 0 _ _ hwfMl hwfMr
    refine ⟨fun j hj => (IntTrie.wellFormed_and_eval_merge (cValJ j) 8 1 0 _ _ (hwfCJl j hj) (hwfCJr j hj)).1,
      fun j hj => (IntTrie.wellFormed_and_eval_merge (mValForJ f j) 10 1 0 _ _ (hwfMJl j hj) (hwfMJr j hj)).1,
      hwfC, hwfM, ?_⟩
    dsimp only [IntTrie.mergeTree]
    rw [hevC, hevM]
    have hadd : (IntTrie.evalTrie cVal 1 0 (IntTrie.mergeTree (psdStepC n d) l) +
          IntTrie.evalTrie cVal 1 0 (IntTrie.mergeTree (psdStepC n d) r)) +
        (IntTrie.evalTrie (terwMVal f) 1 0 (IntTrie.mergeTree (psdStepM n) l) +
          IntTrie.evalTrie (terwMVal f) 1 0 (IntTrie.mergeTree (psdStepM n) r)) =
        (IntTrie.evalTrie cVal 1 0 (IntTrie.mergeTree (psdStepC n d) l) +
          IntTrie.evalTrie (terwMVal f) 1 0 (IntTrie.mergeTree (psdStepM n) l)) +
        (IntTrie.evalTrie cVal 1 0 (IntTrie.mergeTree (psdStepC n d) r) +
          IntTrie.evalTrie (terwMVal f) 1 0 (IntTrie.mergeTree (psdStepM n) r)) := by ring
    rw [hadd, hsuml, hsumr, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j hj
    have hjn : j ≤ n := by rw [Finset.mem_range] at hj; omega
    have h1 := (IntTrie.wellFormed_and_eval_merge (cValJ j) 8 1 0 _ _ (hwfCJl j hjn) (hwfCJr j hjn)).2
    have h2 := (IntTrie.wellFormed_and_eval_merge (mValForJ f j) 10 1 0 _ _ (hwfMJl j hjn) (hwfMJr j hjn)).2
    rw [h1, h2]; ring

/-- **Soundness of `j`-Sliced Step-3 PSD+Binomial Farkas Checker**:
Each layer `j ≤ n` is verified independently via a small depth-10 → depth-8 `by decide` lemma. -/
theorem false_of_psd_bino_farkas_sliced {n d : ℕ} (f : BooleanFun n)
    (hf : polyDegree f ≤ d)
    (S : ℕ → ℕ) (hS : ∀ k ≤ n, realLayerSum (fun x => boolToReal (f x)) k = (S k : ℝ))
    (tree : BinTree PsdBinoStep)
    (hhdr : checkPsdBinoFarkasHeader n d S tree = true)
    (hslices : ∀ j ≤ n, checkPsdBinoSlice n d j tree [] 0 = true) : False := by
  unfold checkPsdBinoFarkasHeader at hhdr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hhdr
  obtain ⟨⟨⟨hn, hd⟩, hok⟩, hpos⟩ := hhdr
  obtain ⟨c, hc, _, _, hle⟩ := psdTree_sound f hn hd hf S hS tree hok
  obtain ⟨hwfCJ, _, _, _, hsumAll⟩ := psdTreeForJ_wf_and_sum f c hn hd tree hok
  have hzero : ∑ j ∈ Finset.range (n + 1),
      (IntTrie.evalTrie (fun idx => c j (idx % 16) (idx / 16)) 1 0
        (IntTrie.mergeTree (psdStepCForJ n d j) tree) +
       IntTrie.evalTrie (mValForJ f j) 1 0
        (IntTrie.mergeTree (psdStepMForJ n j) tree)) = 0 := by
    apply Finset.sum_eq_zero; intro j hj
    have hjn : j ≤ n := by rw [Finset.mem_range] at hj; omega
    have hsl := hslices j hjn
    unfold checkPsdBinoSlice at hsl
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hsl
    obtain ⟨hmOk, hc0⟩ := hsl
    obtain ⟨hwfFromM, hevFromM⟩ := expandMTrieForJ_sound f hd j hjn c hc
      (IntTrie.mergeTree (psdStepMForJ n j) tree) 1 0 hmOk
    obtain ⟨_, hevAll⟩ := IntTrie.wellFormed_and_eval_merge
      (fun idx => c j (idx % 16) (idx / 16)) 8 1 0 _ _ (hwfCJ j hjn) hwfFromM
    rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hc0, hevFromM] at hevAll
    exact hevAll.symm
  rw [hsumAll, hzero] at hle
  have hposR : (0 : ℝ) < (tree.sumZ (psdStepObj n S) : ℝ) := by exact_mod_cast hpos
  linarith

/-- **Soundness of `j`-Sliced Step-3 PSD+Binomial Linear Bound Checker**:
Each layer `j ≤ n` is verified independently via a small depth-10 → depth-8 `by decide` lemma. -/
theorem targetM_bound_of_psd_bino_sliced {n d : ℕ} (f : BooleanFun n)
    (hf : polyDegree f ≤ d)
    (S : ℕ → ℕ) (hS : ∀ k ≤ n, realLayerSum (fun x => boolToReal (f x)) k = (S k : ℝ))
    (tree : BinTree PsdBinoStep)
    (targetM : List (ℕ × ℕ × ℕ × ℤ)) (scale : ℕ) (expectedLb : ℤ)
    (hhdr : checkPsdBinoBoundHeader n d S tree targetM expectedLb = true)
    (hslices : ∀ j ≤ n, checkPsdBinoSlice n d j tree targetM scale = true) :
    (expectedLb : ℝ) ≤ (scale : ℝ) * evalTargetM f targetM := by
  unfold checkPsdBinoBoundHeader at hhdr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hhdr
  obtain ⟨⟨⟨⟨hn, hd⟩, htm⟩, hok⟩, hlb⟩ := hhdr
  have htm' : ∀ q ∈ targetM, ValidTriple n q.1 q.2.1 q.2.2.1 :=
    fun q hq => (validTripleB_iff n q.1 q.2.1 q.2.2.1).mp (htm q hq)
  obtain ⟨c, hc, _, _, hle⟩ := psdTree_sound f hn hd hf S hS tree hok
  obtain ⟨hwfCJ, hwfMJ, _, _, hsumAll⟩ := psdTreeForJ_wf_and_sum f c hn hd tree hok
  let mSub : ℕ → IntTrie := fun j =>
    if scale == 0 then IntTrie.mergeTree (psdStepMForJ n j) tree
    else addMListForJ j (-(scale : ℤ)) targetM (IntTrie.mergeTree (psdStepMForJ n j) tree)
  have hzero : ∑ j ∈ Finset.range (n + 1),
      (IntTrie.evalTrie (fun idx => c j (idx % 16) (idx / 16)) 1 0
        (IntTrie.mergeTree (psdStepCForJ n d j) tree) +
       IntTrie.evalTrie (mValForJ f j) 1 0 (mSub j)) = 0 := by
    apply Finset.sum_eq_zero; intro j hj
    have hjn : j ≤ n := by rw [Finset.mem_range] at hj; omega
    have hsl := hslices j hjn
    unfold checkPsdBinoSlice at hsl
    simp only [Bool.and_eq_true] at hsl
    obtain ⟨hmOk, hc0⟩ := hsl
    obtain ⟨hwfFromM, hevFromM⟩ := expandMTrieForJ_sound f hd j hjn c hc (mSub j) 1 0 hmOk
    obtain ⟨_, hevAll⟩ := IntTrie.wellFormed_and_eval_merge
      (fun idx => c j (idx % 16) (idx / 16)) 8 1 0 _ _ (hwfCJ j hjn) hwfFromM
    rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hc0, hevFromM] at hevAll
    exact hevAll.symm
  have hmSub_sum : ∑ j ∈ Finset.range (n + 1), IntTrie.evalTrie (mValForJ f j) 1 0 (mSub j) =
      (∑ j ∈ Finset.range (n + 1),
        IntTrie.evalTrie (mValForJ f j) 1 0 (IntTrie.mergeTree (psdStepMForJ n j) tree)) -
      (scale : ℝ) * evalTargetM f targetM := by
    by_cases hsc : scale = 0
    · subst hsc; simp [mSub]
    · have hbf : (scale == 0) = false := by simp [hsc]
      have hcongr : ∑ j ∈ Finset.range (n + 1), IntTrie.evalTrie (mValForJ f j) 1 0 (mSub j) =
          ∑ j ∈ Finset.range (n + 1), IntTrie.evalTrie (mValForJ f j) 1 0
            (addMListForJ j (-(scale : ℤ)) targetM (IntTrie.mergeTree (psdStepMForJ n j) tree)) := by
        apply Finset.sum_congr rfl; intro j _; simp [mSub, hbf]
      rw [hcongr]
      obtain ⟨_, hsumM⟩ := addMListForJ_wf_and_sum f hn (-(scale : ℤ)) targetM
        (fun j => IntTrie.mergeTree (psdStepMForJ n j) tree) htm' hwfMJ
      rw [hsumM]; push_cast; ring
  rw [Finset.sum_add_distrib, hmSub_sum] at hzero
  rw [Finset.sum_add_distrib] at hsumAll
  have hlbR : (expectedLb : ℝ) ≤ (tree.sumZ (psdStepObj n S) : ℝ) := by exact_mod_cast hlb
  linarith

end DegreeSensitivity
