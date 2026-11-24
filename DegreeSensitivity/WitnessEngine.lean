module

public import DegreeSensitivity.Multilinear
public import DegreeSensitivity.Sensitivity

@[expose] public section

/-!
# Fast Kernel-Checked Witness Verification Engine (`BoolTree` & `CubeTree`)

Provides a complete-binary-tree representation of Boolean functions (`BoolTree n`)
and integer-valued hypercube tables (`CubeTree n`), equipped with an `O(n · 2^n)`
exact integer Fast Möbius Transform (`CubeTree.mobius`) and its inverse
(`CubeTree.zeta`).

This enables pure kernel-checked verification (via `decide` / `rfl`, with ZERO
`native_decide` and ONLY standard axioms) of:
1. Exact polynomial degree bounds `polyDegree f ≤ d` for arbitrary Boolean functions.
2. Weighted multilinear degree bounds `∀ S, D < ∑ i ∈ S, w i → mobiusCoeff f S = 0`
   for weighted-degree outer functions (e.g. the 9-bit outer function for `(n=13, d=5)`).
3. Normalization `f (zeroVec n) = false ∧ ∀ i, f (basisVec i) = true` (hence `s(f) = n`).
-/

namespace DegreeSensitivity

open scoped BigOperators

/-- Complete binary tree of depth `n` storing a Boolean truth table of size `2^n`. -/
inductive BoolTree : ℕ → Type
  | leaf (b : Bool) : BoolTree 0
  | node {n : ℕ} (lo hi : BoolTree n) : BoolTree (n + 1)

/-- Complete binary tree of depth `n` storing an integer table of size `2^n`. -/
inductive CubeTree : ℕ → Type
  | leaf (v : ℤ) : CubeTree 0
  | node {n : ℕ} (lo hi : CubeTree n) : CubeTree (n + 1)

/-- Evaluate a `BoolTree n` on `x : Fin n → Bool`. -/
def BoolTree.eval : {n : ℕ} → BoolTree n → BooleanFun n
  | 0, .leaf b, _ => b
  | _ + 1, .node lo hi, x => if x 0 then hi.eval (fun i => x i.succ) else lo.eval (fun i => x i.succ)

/-- Build a `BoolTree n` from a list of `2^n` Booleans (first half `x 0 = false`, second half `x 0 = true`). -/
def BoolTree.ofList : (n : ℕ) → List Bool → BoolTree n
  | 0, b :: _ => .leaf b
  | 0, [] => .leaf false
  | n + 1, l =>
      let half := 2 ^ n
      .node (BoolTree.ofList n (l.take half)) (BoolTree.ofList n (l.drop half))

/-- Convert a `BoolTree n` to its `{0, 1}`-valued `CubeTree n`. -/
def BoolTree.toCubeTree : {n : ℕ} → BoolTree n → CubeTree n
  | 0, .leaf b => .leaf (boolToInt b)
  | _ + 1, .node lo hi => .node lo.toCubeTree hi.toCubeTree

/-- Evaluate a `CubeTree n` on `x : Fin n → Bool`. -/
def CubeTree.eval : {n : ℕ} → CubeTree n → (Fin n → Bool) → ℤ
  | 0, .leaf v, _ => v
  | _ + 1, .node lo hi, x => if x 0 then hi.eval (fun i => x i.succ) else lo.eval (fun i => x i.succ)

lemma eval_toCubeTree : ∀ {n : ℕ} (bt : BoolTree n) (x : Fin n → Bool),
    bt.toCubeTree.eval x = boolToInt (bt.eval x)
  | 0, .leaf _, _ => rfl
  | _ + 1, .node lo hi, x => by
      simp only [BoolTree.toCubeTree, CubeTree.eval, BoolTree.eval]
      cases x 0
      · exact eval_toCubeTree lo (fun i => x i.succ)
      · exact eval_toCubeTree hi (fun i => x i.succ)

/-- Pointwise addition of `CubeTree n`. -/
def CubeTree.add : {n : ℕ} → CubeTree n → CubeTree n → CubeTree n
  | 0, .leaf a, .leaf b => .leaf (a + b)
  | _ + 1, .node l1 h1, .node l2 h2 => .node (l1.add l2) (h1.add h2)

/-- Pointwise subtraction of `CubeTree n`. -/
def CubeTree.sub : {n : ℕ} → CubeTree n → CubeTree n → CubeTree n
  | 0, .leaf a, .leaf b => .leaf (a - b)
  | _ + 1, .node l1 h1, .node l2 h2 => .node (l1.sub l2) (h1.sub h2)

lemma CubeTree.eval_add : ∀ {n : ℕ} (a b : CubeTree n) (x : Fin n → Bool),
    (a.add b).eval x = a.eval x + b.eval x
  | 0, .leaf _, .leaf _, _ => rfl
  | _ + 1, .node l1 h1, .node l2 h2, x => by
      simp only [CubeTree.add, CubeTree.eval]
      cases x 0
      · exact CubeTree.eval_add l1 l2 _
      · exact CubeTree.eval_add h1 h2 _

lemma CubeTree.add_sub_cancel : ∀ {n : ℕ} (a b : CubeTree n),
    a.add (b.sub a) = b
  | 0, .leaf u, .leaf v => by simp [CubeTree.add, CubeTree.sub]
  | _ + 1, .node l1 h1, .node l2 h2 => by
      simp [CubeTree.add, CubeTree.sub, CubeTree.add_sub_cancel l1 l2, CubeTree.add_sub_cancel h1 h2]

/-- Fast Möbius Transform on `CubeTree n` (`O(n · 2^n)` integer subtractions,
written linearly as `node lo.mobius (hi.sub lo).mobius` so call-by-name kernel
reduction never duplicates `lo.mobius`!). -/
def CubeTree.mobius : {n : ℕ} → CubeTree n → CubeTree n
  | 0, .leaf v => .leaf v
  | _ + 1, .node lo hi => .node lo.mobius (hi.sub lo).mobius

/-- Fast Zeta Transform (inverse Möbius transform / multilinear evaluation) on `CubeTree n`,
written linearly as `node lo.zeta (lo.add hi).zeta` so call-by-name kernel reduction
never duplicates `lo.zeta`. -/
def CubeTree.zeta : {n : ℕ} → CubeTree n → CubeTree n
  | 0, .leaf v => .leaf v
  | _ + 1, .node lo hi => .node lo.zeta (lo.add hi).zeta

lemma CubeTree.add_comm : ∀ {n : ℕ} (a b : CubeTree n), a.add b = b.add a
  | 0, .leaf u, .leaf v => by simp [CubeTree.add, Int.add_comm]
  | _ + 1, .node l1 h1, .node l2 h2 => by
      simp [CubeTree.add, CubeTree.add_comm l1 l2, CubeTree.add_comm h1 h2]

lemma CubeTree.add_assoc : ∀ {n : ℕ} (a b c : CubeTree n),
    (a.add b).add c = a.add (b.add c)
  | 0, .leaf u, .leaf v, .leaf w => by simp [CubeTree.add, Int.add_assoc]
  | _ + 1, .node l1 h1, .node l2 h2, .node l3 h3 => by
      simp [CubeTree.add, CubeTree.add_assoc l1 l2 l3, CubeTree.add_assoc h1 h2 h3]

lemma CubeTree.add_add_add_comm : ∀ {n : ℕ} (a b c d : CubeTree n),
    (a.add b).add (c.add d) = (a.add c).add (b.add d)
  | 0, .leaf _, .leaf _, .leaf _, .leaf _ => by simp [CubeTree.add]; ring
  | _ + 1, .node _ _, .node _ _, .node _ _, .node _ _ => by
      simp [CubeTree.add, CubeTree.add_add_add_comm]

lemma CubeTree.sub_add_sub_comm : ∀ {n : ℕ} (a b c d : CubeTree n),
    (a.sub b).add (c.sub d) = (a.add c).sub (b.add d)
  | 0, .leaf _, .leaf _, .leaf _, .leaf _ => by simp [CubeTree.add, CubeTree.sub]; ring
  | _ + 1, .node _ _, .node _ _, .node _ _, .node _ _ => by
      simp [CubeTree.add, CubeTree.sub, CubeTree.sub_add_sub_comm]

lemma CubeTree.zeta_add : ∀ {n : ℕ} (a b : CubeTree n),
    (a.add b).zeta = a.zeta.add b.zeta
  | 0, .leaf _, .leaf _ => rfl
  | _ + 1, .node l1 h1, .node l2 h2 => by
      simp only [CubeTree.add, CubeTree.zeta, CubeTree.zeta_add]
      congr 1
      exact CubeTree.add_add_add_comm _ _ _ _

lemma CubeTree.zeta_sub : ∀ {n : ℕ} (a b : CubeTree n),
    (a.sub b).zeta = a.zeta.sub b.zeta
  | 0, .leaf _, .leaf _ => rfl
  | _ + 1, .node l1 h1, .node l2 h2 => by
      simp only [CubeTree.sub, CubeTree.zeta, CubeTree.zeta_sub]
      congr 1
      rw [CubeTree.sub_add_sub_comm, CubeTree.zeta_sub]

theorem CubeTree.zeta_mobius : ∀ {n : ℕ} (t : CubeTree n), t.mobius.zeta = t
  | 0, .leaf _ => rfl
  | _ + 1, .node lo hi => by
      simp only [CubeTree.mobius, CubeTree.zeta]
      rw [CubeTree.zeta_mobius lo, CubeTree.zeta_add, CubeTree.zeta_mobius lo,
        CubeTree.zeta_mobius (hi.sub lo), CubeTree.add_sub_cancel]

/-- Fundamental evaluation theorem for `CubeTree.zeta`:
`c.zeta.eval x = ∑ S ∈ (supportOf x).powerset, c.eval (indicator S)`. -/
theorem CubeTree.eval_zeta : ∀ {n : ℕ} (c : CubeTree n) (x : Fin n → Bool),
    (c.zeta.eval x : ℝ) = ∑ S ∈ (supportOf x).powerset, (c.eval (indicator S) : ℝ)
  | 0, .leaf v, x => by
      have hsupp : supportOf x = ∅ := by ext i; exact i.elim0
      simp [CubeTree.zeta, CubeTree.eval, hsupp]
  | n + 1, .node lo hi, x => by
      let x' : Fin n → Bool := fun i => x i.succ
      have htail : (supportOf x).erase 0 = (supportOf x').image Fin.succ := by
        ext j
        refine Fin.cases ?_ ?_ j
        · simp [Fin.succ_ne_zero]
        · intro i
          simp [Fin.succ_ne_zero, x']
      have h0not : (0 : Fin (n + 1)) ∉ (supportOf x').image Fin.succ := by
        simp [Fin.succ_ne_zero]
      have hlo_img : ∀ T : Finset (Fin n),
          (CubeTree.node lo hi).eval (indicator (T.image Fin.succ)) = lo.eval (indicator T) := by
        intro T
        have h0 : indicator (T.image Fin.succ) 0 = false := by
          simp [indicator, Fin.succ_ne_zero]
        have hrest : (fun i : Fin n => indicator (T.image Fin.succ) i.succ) = indicator T := by
          funext i
          simp [indicator, Fin.succ_inj]
        simp [CubeTree.eval, h0, hrest]
      have hhi_img : ∀ T : Finset (Fin n),
          (CubeTree.node lo hi).eval (indicator (insert 0 (T.image Fin.succ))) =
            hi.eval (indicator T) := by
        intro T
        have h0 : indicator (insert 0 (T.image Fin.succ)) 0 = true := by
          simp [indicator]
        have hrest : (fun i : Fin n => indicator (insert 0 (T.image Fin.succ)) i.succ) =
            indicator T := by
          funext i
          simp [indicator, Fin.succ_ne_zero, Fin.succ_inj]
        simp [CubeTree.eval, h0, hrest]
      have hpow_img : ∀ (F : Finset (Fin (n + 1)) → ℝ),
          ∑ S ∈ ((supportOf x').image Fin.succ).powerset, F S =
            ∑ T ∈ (supportOf x').powerset, F (T.image Fin.succ) := by
        intro F
        classical
        rw [← Finset.sum_image (g := fun T : Finset (Fin n) => T.image Fin.succ)]
        · apply Finset.sum_congr _ (fun _ _ => rfl)
          ext S
          simp only [Finset.mem_powerset, Finset.mem_image]
          constructor
          · intro hS
            refine ⟨(supportOf x').filter (fun i => i.succ ∈ S), Finset.filter_subset _ _, ?_⟩
            ext j
            simp only [Finset.mem_image, Finset.mem_filter]
            constructor
            · rintro ⟨i, ⟨_, hiS⟩, rfl⟩; exact hiS
            · intro hj
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hS hj)
              exact ⟨i, ⟨hi, hj⟩, rfl⟩
          · rintro ⟨T, hT, rfl⟩
            exact Finset.image_subset_image hT
        · intro T₁ _ T₂ _ hEq
          exact Finset.image_injective (Fin.succ_injective n) hEq
      cases hx0 : x 0
      · have hsupp : supportOf x = (supportOf x').image Fin.succ := by
          have hnot0 : (0 : Fin (n + 1)) ∉ supportOf x := by simp [hx0]
          rw [← Finset.erase_eq_of_notMem hnot0, htail]
        have hlhs : ((CubeTree.node lo hi).zeta.eval x : ℝ) = (lo.zeta.eval x' : ℝ) := by
          simp [CubeTree.zeta, CubeTree.eval, hx0, x']
        rw [hlhs, hsupp, hpow_img, CubeTree.eval_zeta lo x']
        apply Finset.sum_congr rfl
        intro T _
        rw [hlo_img T]
      · have hsupp : supportOf x = insert 0 ((supportOf x').image Fin.succ) := by
          have hmem0 : (0 : Fin (n + 1)) ∈ supportOf x := mem_supportOf.mpr hx0
          rw [← htail, Finset.insert_erase hmem0]
        have hlhs : ((CubeTree.node lo hi).zeta.eval x : ℝ) =
            (lo.zeta.eval x' : ℝ) + (hi.zeta.eval x' : ℝ) := by
          simp [CubeTree.zeta, CubeTree.eval, hx0, CubeTree.zeta_add, CubeTree.eval_add, x']
        rw [hlhs, hsupp, Finset.powerset_insert]
        have hdisj : Disjoint ((supportOf x').image Fin.succ).powerset
            (((supportOf x').image Fin.succ).powerset.image (insert 0)) := by
          rw [Finset.disjoint_left]
          intro S hS1 hS2
          rw [Finset.mem_image] at hS2
          obtain ⟨T, _, rfl⟩ := hS2
          exact h0not (Finset.mem_powerset.mp hS1 (Finset.mem_insert_self 0 T))
        rw [Finset.sum_union hdisj, Finset.sum_image]
        · rw [hpow_img, hpow_img, CubeTree.eval_zeta lo x', CubeTree.eval_zeta hi x']
          congr 1
          · apply Finset.sum_congr rfl; intro T _; rw [hlo_img T]
          · apply Finset.sum_congr rfl; intro T _; rw [hhi_img T]
        · intro T₁ hT₁ T₂ hT₂ hEq
          have h1 : (0 : Fin (n + 1)) ∉ T₁ := fun h => h0not (Finset.mem_powerset.mp hT₁ h)
          have h2 : (0 : Fin (n + 1)) ∉ T₂ := fun h => h0not (Finset.mem_powerset.mp hT₂ h)
          have := congrArg (fun S => S.erase 0) hEq
          simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this

/-- **Exact Möbius Correspondence**: The Fast Möbius Transform `bt.toCubeTree.mobius`
computes `mobiusCoeff bt.eval S` for every subset `S : Finset (Fin n)`. -/
theorem eval_mobius_eq_mobiusCoeff {n : ℕ} (bt : BoolTree n) (S : Finset (Fin n)) :
    bt.toCubeTree.mobius.eval (indicator S) = mobiusCoeff bt.eval S := by
  have hrep : RepresentsPoly (multilinearPoly (fun T => (bt.toCubeTree.mobius.eval (indicator T) : ℝ)))
      bt.eval := by
    intro x
    change MvPolynomial.eval (fun i => boolToReal (x i))
      (multilinearPoly (fun T => (bt.toCubeTree.mobius.eval (indicator T) : ℝ))) =
      boolToReal (bt.eval x)
    rw [eval_multilinearPoly, ← CubeTree.eval_zeta, CubeTree.zeta_mobius, eval_toCubeTree,
      boolToReal_eq_cast]
  have hu := multilinear_coeff_unique hrep S
  exact_mod_cast hu

/-- Fast recursive weighted-degree checker using a flat `List ℕ` of weights
(avoids `Fin.succ` / `Matrix.vecCons` closure buildup during kernel reduction). -/
def CubeTree.checkWeightedDegList : {n : ℕ} → List ℕ → ℕ → ℕ → CubeTree n → Bool
  | 0, _, acc, D, .leaf v => decide (acc ≤ D) || (v == 0)
  | _ + 1, w0 :: ws, acc, D, .node lo hi =>
      lo.checkWeightedDegList ws acc D && hi.checkWeightedDegList ws (acc + w0) D
  | _ + 1, [], _, _, _ => false

lemma CubeTree.eq_zero_of_checkWeightedDegList :
    ∀ {n : ℕ} (c : CubeTree n) (ws : List ℕ) (w : Fin n → ℕ)
      (_hw : ∀ i : Fin n, ws[i.1]? = some (w i)) (acc D : ℕ),
      c.checkWeightedDegList ws acc D = true →
      ∀ S : Finset (Fin n), D < acc + ∑ i ∈ S, w i → c.eval (indicator S) = 0
  | 0, .leaf v, _, _, _, acc, D, hchk, S, hgt => by
      simp only [Finset.eq_empty_of_isEmpty S, Finset.sum_empty, add_zero] at hgt
      simp only [CubeTree.checkWeightedDegList, Bool.or_eq_true, decide_eq_true_eq,
        beq_iff_eq] at hchk
      rcases hchk with hle | hv
      · omega
      · exact hv
  | n + 1, .node lo hi, [], _, _, _, _, hchk, _, _ => by
      simp [CubeTree.checkWeightedDegList] at hchk
  | n + 1, .node lo hi, w0 :: ws, w, hw, acc, D, hchk, S, hgt => by
      simp only [CubeTree.checkWeightedDegList, Bool.and_eq_true] at hchk
      obtain ⟨hlo, hhi⟩ := hchk
      have hw0 : w0 = w 0 := by
        have h0 := hw 0
        simp at h0
        exact h0
      have hws : ∀ i : Fin n, ws[i.1]? = some (w i.succ) := fun i => by
        simpa using hw i.succ
      let S' : Finset (Fin n) := Finset.univ.filter (fun i => i.succ ∈ S)
      have hrest : (fun i : Fin n => indicator S i.succ) = indicator S' := by
        funext i; simp [indicator, S']
      by_cases h0 : (0 : Fin (n + 1)) ∈ S
      · have hS : S = insert 0 (S'.image Fin.succ) := by
          ext j
          refine Fin.cases ?_ ?_ j
          · simp [h0]
          · intro i; simp [S', Fin.succ_ne_zero, Fin.succ_inj]
        have h0not : (0 : Fin (n + 1)) ∉ S'.image Fin.succ := by simp [Fin.succ_ne_zero]
        have hsum : ∑ i ∈ S, w i = w 0 + ∑ i ∈ S', w i.succ := by
          conv_lhs => rw [hS]
          rw [Finset.sum_insert h0not, Finset.sum_image (fun _ _ _ _ h => Fin.succ_injective n h)]
        have hgt' : D < (acc + w0) + ∑ i ∈ S', w i.succ := by omega
        simp only [CubeTree.eval, indicator, h0, decide_true, ↓reduceIte]
        rw [show (fun i : Fin n => decide (i.succ ∈ S)) = indicator S' from hrest]
        exact CubeTree.eq_zero_of_checkWeightedDegList hi ws (fun i => w i.succ) hws
          (acc + w0) D hhi S' hgt'
      · have hS : S = S'.image Fin.succ := by
          ext j
          refine Fin.cases ?_ ?_ j
          · simp [h0, Fin.succ_ne_zero]
          · intro i; simp [S', Fin.succ_inj]
        have hsum : ∑ i ∈ S, w i = ∑ i ∈ S', w i.succ := by
          conv_lhs => rw [hS]
          rw [Finset.sum_image (fun _ _ _ _ h => Fin.succ_injective n h)]
        have hgt' : D < acc + ∑ i ∈ S', w i.succ := by omega
        simp only [CubeTree.eval, indicator, h0, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [show (fun i : Fin n => decide (i.succ ∈ S)) = indicator S' from hrest]
        exact CubeTree.eq_zero_of_checkWeightedDegList lo ws (fun i => w i.succ) hws
          acc D hlo S' hgt'

/-- Decomposition lemma for `CubeTree.mobius`: allows staging `hi.sub lo = d` into an explicit
literal tree `d`, avoiding thunk duplication during kernel reduction on larger dimensions. -/
theorem CubeTree.checkWeightedDegList_node_mobius {n : ℕ} (lo hi d : CubeTree n)
    (w0 : ℕ) (ws : List ℕ) (acc D : ℕ)
    (hd : hi.sub lo = d)
    (hlo : lo.mobius.checkWeightedDegList ws acc D = true)
    (hhi : d.mobius.checkWeightedDegList ws (acc + w0) D = true) :
    (CubeTree.node lo hi).mobius.checkWeightedDegList (w0 :: ws) acc D = true := by
  simp [CubeTree.mobius, CubeTree.checkWeightedDegList, hd, hlo, hhi]

/-- **Weighted Degree Verification Theorem**:
If `bt.toCubeTree.mobius.checkWeightedDegList ws 0 D = true` where `ws` lists the weights `w`,
then every Möbius coefficient of `bt.eval` with total weight `> D` vanishes. -/
theorem mobiusCoeff_eq_zero_of_checkWeightedDeg {n : ℕ} (bt : BoolTree n)
    (ws : List ℕ) (w : Fin n → ℕ) (hw : ∀ i : Fin n, ws[i.1]? = some (w i)) (D : ℕ)
    (hchk : bt.toCubeTree.mobius.checkWeightedDegList ws 0 D = true) :
    ∀ S : Finset (Fin n), D < ∑ i ∈ S, w i → mobiusCoeff bt.eval S = 0 := by
  intro S hS
  rw [← eval_mobius_eq_mobiusCoeff bt S]
  exact CubeTree.eq_zero_of_checkWeightedDegList bt.toCubeTree.mobius ws w hw 0 D hchk S
    (by simpa using hS)

/-- **Standard Degree Verification Theorem**:
If `bt.toCubeTree.mobius.checkWeightedDegList (List.replicate n 1) 0 d = true`, then
`polyDegree bt.eval ≤ d`. -/
theorem polyDegree_le_of_checkDeg {n d : ℕ} (bt : BoolTree n)
    (hchk : bt.toCubeTree.mobius.checkWeightedDegList (List.replicate n 1) 0 d = true) :
    polyDegree bt.eval ≤ d := by
  rw [polyDegree_eq_mobiusDegree, mobiusDegree, Finset.sup_le_iff]
  intro S hS
  have hne : mobiusCoeff bt.eval S ≠ 0 := (Finset.mem_filter.mp hS).2
  by_contra hgt
  have hlt : d < ∑ _i ∈ S, (1 : ℕ) := by simp; omega
  have hw : ∀ i : Fin n, (List.replicate n 1)[i.1]? = some 1 := fun i => by
    simp [i.2]
  exact hne (mobiusCoeff_eq_zero_of_checkWeightedDeg bt (List.replicate n 1) (fun _ => 1) hw d hchk S hlt)

/-- Decidable check that `bt.eval` is normalized (`f 0 = false` and `∀ i, f (e_i) = true`). -/
def BoolTree.checkNormalized {n : ℕ} (bt : BoolTree n) : Bool :=
  (!bt.eval (zeroVec n)) && (List.finRange n).all (fun i => bt.eval (basisVec i))

theorem BoolTree.normalized_of_check {n : ℕ} (bt : BoolTree n)
    (h : bt.checkNormalized = true) :
    bt.eval (zeroVec n) = false ∧ ∀ i : Fin n, bt.eval (basisVec i) = true := by
  simp only [BoolTree.checkNormalized, Bool.and_eq_true, Bool.not_eq_true',
    List.all_eq_true, List.mem_finRange, forall_const] at h
  exact h

end DegreeSensitivity
