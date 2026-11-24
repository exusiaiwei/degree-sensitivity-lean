module

public import DegreeSensitivity.TerwilligerCore

@[expose] public section

/-!
# Pure-Integer Sparse Binary Trie LP/Farkas Verification Engines

Fast, shallow-recursion (`maxRecDepth ≤ 35`), kernel-checked (`by decide`) pure-integer dual/Farkas
LP verifiers built on a sparse binary trie `IntTrie` and balanced binary certificate trees `BinTree`:

1. **`BinomialBasisLP` (`checkBinoFarkas`, `checkBinoBound`)**:
   Verifies Farkas infeasibility certificates and exact linear bounds on `layerAvg f objK` in the
   univariate + bivariate binomial basis (`u_r`, `c_{j,r,s}`) of the Subset-`J` Terwilliger LP.
   Powers the new world records `B_7 ≤ 28`, `B_8 ≤ 36`, `B_9 ≤ 46`, and Steps 1–2 of `B_6 ≤ 20`.

2. **`TerwLPBound` (`checkTerwLPBound`)**:
   Verifies exact linear lower bounds on `p(k)` and `m(i, j, t)` in the full joint Terwilliger LP
   (univariate/bivariate finite differences, diagonal/boundary equalities, Fréchet/McCormick
   inequalities, layer-product equalities, fixed layer sums, and custom proved linear equalities).
   Powers all 4 LP certificates in the new world record `B_5 ≤ 14` (`(15, 5)` impossibility).

Using balanced binary trees `BinTree` with pointwise `IntTrie.merge` keeps kernel WHNF recursion
depth logarithmic (`≤ 35`), completely avoiding `maxRecDepth` overflows and thunk duplication across
Lean's kernel, `nanoda`, and `con-ron`.
-/

namespace DegreeSensitivity

open scoped BigOperators

/-! ### Part 1: Fast `O(r)` Binomial Coefficients & Balanced Certificate Trees -/

/-- Auxiliary `O(r)` recurrence for `Nat.choose k r`: `C(k, r + 1) = C(k, r) * (k - r) / (r + 1)`. -/
def fastChooseAux (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => fastChooseAux k r * (k - r) / (r + 1)

/-- Fast `O(r)` kernel-computable binomial coefficient equal to `Nat.choose k r`. -/
def fastChoose (k r : ℕ) : ℕ :=
  if r ≤ k then fastChooseAux k r else 0

lemma choose_step_div (k r : ℕ) :
    Nat.choose k r * (k - r) / (r + 1) = Nat.choose k (r + 1) := by
  have h := Nat.choose_succ_right_eq k r
  rw [← h, mul_comm (Nat.choose k (r + 1)) (r + 1)]
  exact Nat.mul_div_cancel_left (Nat.choose k (r + 1)) (Nat.succ_pos r)

lemma fastChooseAux_eq (k r : ℕ) : fastChooseAux k r = Nat.choose k r := by
  induction r with
  | zero => simp [fastChooseAux]
  | succ r ih =>
    simp only [fastChooseAux, ih]
    exact choose_step_div k r

lemma fastChoose_eq (k r : ℕ) : fastChoose k r = Nat.choose k r := by
  unfold fastChoose
  split_ifs with h
  · exact fastChooseAux_eq k r
  · exact (Nat.choose_eq_zero_of_lt (by omega)).symm

/-- Integer sign `(-1)^m` computed without exponentiation. -/
def altSign (m : ℕ) : ℤ :=
  if m % 2 == 0 then 1 else -1

lemma altSign_eq (m : ℕ) : altSign m = (-1 : ℤ) ^ m := by
  unfold altSign
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · have hmod : (2 * k) % 2 = 0 := by omega
    simp [hmod, pow_mul]
  · have hmod : (2 * k + 1) % 2 = 1 := by omega
    simp [hmod, pow_succ, pow_mul]

/-- Balanced binary tree of certificate steps (keeps kernel WHNF recursion depth logarithmic). -/
inductive BinTree (α : Type*) where
  | empty : BinTree α
  | leaf : α → BinTree α
  | node : BinTree α → BinTree α → BinTree α
  deriving Repr, DecidableEq

namespace BinTree

def all {α : Type*} (p : α → Bool) : BinTree α → Bool
  | .empty => true
  | .leaf a => p a
  | .node l r => all p l && all p r

def sumZ {α : Type*} (f : α → ℤ) : BinTree α → ℤ
  | .empty => 0
  | .leaf a => f a
  | .node l r => sumZ f l + sumZ f r

end BinTree

/-! ### Part 2: Sparse Binary Integer Trie (`IntTrie`) -/

/-- Sparse binary trie storing `ℤ` coefficients at fixed depth. -/
inductive IntTrie where
  | empty : IntTrie
  | leaf : ℤ → IntTrie
  | node : IntTrie → IntTrie → IntTrie
  deriving Repr, DecidableEq

namespace IntTrie

/-- Depth well-formedness invariant: every `leaf` sits at depth `0`, every `node` at `d + 1`. -/
def WellFormed : ℕ → IntTrie → Prop
  | _, .empty => True
  | 0, .leaf _ => True
  | _ + 1, .leaf _ => False
  | 0, .node _ _ => False
  | d + 1, .node lo hi => WellFormed d lo ∧ WellFormed d hi

lemma wellFormed_empty (d : ℕ) : WellFormed d .empty := by
  cases d <;> trivial

/-- Add `delta` to a depth-0 leaf (turning `.empty` into `.leaf delta`). -/
def addLeaf (delta : ℤ) : IntTrie → IntTrie
  | .empty => .leaf delta
  | .leaf v => .leaf (v + delta)
  | t => t

/-- Descend `depth` bits of `idx` (LSB first) and apply `f` to the subtree at that address. -/
def modifyAt : ℕ → ℕ → (IntTrie → IntTrie) → IntTrie → IntTrie
  | 0, _, f, t => f t
  | depth + 1, idx, f, .empty =>
      if idx % 2 == 0 then .node (modifyAt depth (idx / 2) f .empty) .empty
      else .node .empty (modifyAt depth (idx / 2) f .empty)
  | _ + 1, _, _, .leaf v => .leaf v
  | depth + 1, idx, f, .node lo hi =>
      if idx % 2 == 0 then .node (modifyAt depth (idx / 2) f lo) hi
      else .node lo (modifyAt depth (idx / 2) f hi)

/-- Add `delta` at leaf index `idx` in a trie of depth `depth`. -/
def addAt (depth idx : ℕ) (delta : ℤ) (t : IntTrie) : IntTrie :=
  if delta == 0 then t else modifyAt depth idx (addLeaf delta) t

/-- Pointwise sum of two same-depth `IntTrie`s. -/
def merge : IntTrie → IntTrie → IntTrie
  | .empty, t => t
  | t, .empty => t
  | .leaf a, .leaf b => .leaf (a + b)
  | .node l1 r1, .node l2 r2 => .node (merge l1 l2) (merge r1 r2)
  | t, _ => t

/-- Merge tries produced by leaves of a `BinTree`. -/
def mergeTree {α : Type*} (f : α → IntTrie) : BinTree α → IntTrie
  | .empty => .empty
  | .leaf a => f a
  | .node l r => merge (mergeTree f l) (mergeTree f r)

/-- Check whether every stored leaf equals `0`. -/
def isZero : IntTrie → Bool
  | .empty => true
  | .leaf v => v == 0
  | .node lo hi => isZero lo && isZero hi

/-- Evaluate a trie as a linear combination of `val : ℕ → ℝ`. -/
noncomputable def evalTrie (val : ℕ → ℝ) : ℕ → ℕ → IntTrie → ℝ
  | _, _, .empty => 0
  | _, base, .leaf v => (v : ℝ) * val base
  | step, base, .node lo hi =>
      evalTrie val (2 * step) base lo + evalTrie val (2 * step) (base + step) hi

lemma evalTrie_eq_zero_of_isZero (val : ℕ → ℝ) (step base : ℕ) (t : IntTrie)
    (hz : t.isZero = true) : evalTrie val step base t = 0 := by
  induction t generalizing step base with
  | empty => rfl
  | leaf v =>
    simp only [isZero, beq_iff_eq] at hz
    simp [evalTrie, hz]
  | node lo hi ihlo ihhi =>
    simp only [isZero, Bool.and_eq_true] at hz
    simp only [evalTrie, ihlo (2 * step) base hz.1, ihhi (2 * step) (base + step) hz.2, add_zero]

lemma wellFormed_and_eval_merge (val : ℕ → ℝ) (d : ℕ) :
    ∀ step base t1 t2,
      WellFormed d t1 → WellFormed d t2 →
      WellFormed d (merge t1 t2) ∧
        evalTrie val step base (merge t1 t2) =
          evalTrie val step base t1 + evalTrie val step base t2 := by
  induction d with
  | zero =>
    intro step base t1 t2 h1 h2
    cases t1 with
    | empty => simp [merge, evalTrie, h2]
    | leaf a =>
      cases t2 with
      | empty => simp [merge, evalTrie, h1]
      | leaf b =>
        refine ⟨trivial, ?_⟩
        simp only [merge, evalTrie]; push_cast; ring
      | node _ _ => exact False.elim h2
    | node _ _ => exact False.elim h1
  | succ d ih =>
    intro step base t1 t2 h1 h2
    cases t1 with
    | empty => simp [merge, evalTrie, h2]
    | leaf _ => exact False.elim h1
    | node l1 r1 =>
      cases t2 with
      | empty => simp [merge, evalTrie, h1]
      | leaf _ => exact False.elim h2
      | node l2 r2 =>
        obtain ⟨hl1, hr1⟩ := h1
        obtain ⟨hl2, hr2⟩ := h2
        obtain ⟨hwfL, hevL⟩ := ih (2 * step) base l1 l2 hl1 hl2
        obtain ⟨hwfR, hevR⟩ := ih (2 * step) (base + step) r1 r2 hr1 hr2
        refine ⟨⟨hwfL, hwfR⟩, ?_⟩
        simp only [merge, evalTrie, hevL, hevR]; ring

lemma wellFormed_and_eval_addLeaf (val : ℕ → ℝ) (step base : ℕ) (delta : ℤ) (t : IntTrie)
    (hwf : WellFormed 0 t) :
    WellFormed 0 (addLeaf delta t) ∧
      evalTrie val step base (addLeaf delta t) = evalTrie val step base t + (delta : ℝ) * val base := by
  cases t with
  | empty =>
    refine ⟨trivial, ?_⟩
    simp [addLeaf, evalTrie]
  | leaf v =>
    refine ⟨trivial, ?_⟩
    simp only [addLeaf, evalTrie]
    push_cast; ring
  | node _ _ =>
    exact False.elim hwf

lemma wellFormed_and_eval_modifyAt (val : ℕ → ℝ) (d1 d2 idx step base : ℕ) (delta : ℝ)
    (f : IntTrie → IntTrie) (t : IntTrie)
    (hidx : idx < 2 ^ d1) (hwf : WellFormed (d1 + d2) t)
    (hf : ∀ s, WellFormed d2 s →
      WellFormed d2 (f s) ∧
        evalTrie val (2 ^ d1 * step) (base + step * idx) (f s) =
          evalTrie val (2 ^ d1 * step) (base + step * idx) s + delta) :
    WellFormed (d1 + d2) (modifyAt d1 idx f t) ∧
      evalTrie val step base (modifyAt d1 idx f t) = evalTrie val step base t + delta := by
  induction d1 generalizing idx step base t with
  | zero =>
    have hidx0 : idx = 0 := by omega
    subst hidx0
    simp only [Nat.zero_add, pow_zero, one_mul, mul_zero, add_zero] at hwf hf ⊢
    exact hf t hwf
  | succ d1 ih =>
    have hpow : 2 ^ (d1 + 1) = 2 * 2 ^ d1 := by ring
    have hidx' : idx / 2 < 2 ^ d1 := by omega
    have hstep_eq : 2 ^ d1 * (2 * step) = 2 ^ (d1 + 1) * step := by ring
    have hadd_eq : d1 + 1 + d2 = (d1 + d2) + 1 := by omega
    cases t with
    | empty =>
      simp only [modifyAt]
      by_cases hpar : idx % 2 = 0
      · have hbeq : (idx % 2 == 0) = true := by simp [hpar]
        rw [hbeq]; simp only [↓reduceIte]
        have hbase_eq : base + (2 * step) * (idx / 2) = base + step * idx := by
          have : idx = 2 * (idx / 2) := by omega
          calc base + 2 * step * (idx / 2) = base + step * (2 * (idx / 2)) := by ring
            _ = base + step * idx := by rw [← this]
        have hf' : ∀ s, WellFormed d2 s →
            WellFormed d2 (f s) ∧
              evalTrie val (2 ^ d1 * (2 * step)) (base + (2 * step) * (idx / 2)) (f s) =
                evalTrie val (2 ^ d1 * (2 * step)) (base + (2 * step) * (idx / 2)) s + delta := by
          rw [hstep_eq, hbase_eq]; exact hf
        obtain ⟨hwfL, hevL⟩ := ih (idx / 2) (2 * step) base .empty hidx' (wellFormed_empty _) hf'
        refine ⟨?_, ?_⟩
        · rw [hadd_eq]; exact ⟨hwfL, wellFormed_empty _⟩
        · simp only [evalTrie, hevL, zero_add, add_zero]
      · have hbeq : (idx % 2 == 0) = false := by simp [hpar]
        rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hbase_eq : (base + step) + (2 * step) * (idx / 2) = base + step * idx := by
          have : idx = 2 * (idx / 2) + 1 := by omega
          calc base + step + 2 * step * (idx / 2) = base + step * (2 * (idx / 2) + 1) := by ring
            _ = base + step * idx := by rw [← this]
        have hf' : ∀ s, WellFormed d2 s →
            WellFormed d2 (f s) ∧
              evalTrie val (2 ^ d1 * (2 * step)) ((base + step) + (2 * step) * (idx / 2)) (f s) =
                evalTrie val (2 ^ d1 * (2 * step)) ((base + step) + (2 * step) * (idx / 2)) s + delta := by
          rw [hstep_eq, hbase_eq]; exact hf
        obtain ⟨hwfR, hevR⟩ := ih (idx / 2) (2 * step) (base + step) .empty hidx' (wellFormed_empty _) hf'
        refine ⟨?_, ?_⟩
        · rw [hadd_eq]; exact ⟨wellFormed_empty _, hwfR⟩
        · simp only [evalTrie, hevR, zero_add]
    | leaf v =>
      rw [hadd_eq] at hwf
      exact False.elim hwf
    | node lo hi =>
      rw [hadd_eq] at hwf
      obtain ⟨hwfLo, hwfHi⟩ := hwf
      simp only [modifyAt]
      by_cases hpar : idx % 2 = 0
      · have hbeq : (idx % 2 == 0) = true := by simp [hpar]
        rw [hbeq]; simp only [↓reduceIte]
        have hbase_eq : base + (2 * step) * (idx / 2) = base + step * idx := by
          have : idx = 2 * (idx / 2) := by omega
          calc base + 2 * step * (idx / 2) = base + step * (2 * (idx / 2)) := by ring
            _ = base + step * idx := by rw [← this]
        have hf' : ∀ s, WellFormed d2 s →
            WellFormed d2 (f s) ∧
              evalTrie val (2 ^ d1 * (2 * step)) (base + (2 * step) * (idx / 2)) (f s) =
                evalTrie val (2 ^ d1 * (2 * step)) (base + (2 * step) * (idx / 2)) s + delta := by
          rw [hstep_eq, hbase_eq]; exact hf
        obtain ⟨hwfL, hevL⟩ := ih (idx / 2) (2 * step) base lo hidx' hwfLo hf'
        refine ⟨?_, ?_⟩
        · rw [hadd_eq]; exact ⟨hwfL, hwfHi⟩
        · simp only [evalTrie, hevL]; ring
      · have hbeq : (idx % 2 == 0) = false := by simp [hpar]
        rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hbase_eq : (base + step) + (2 * step) * (idx / 2) = base + step * idx := by
          have : idx = 2 * (idx / 2) + 1 := by omega
          calc base + step + 2 * step * (idx / 2) = base + step * (2 * (idx / 2) + 1) := by ring
            _ = base + step * idx := by rw [← this]
        have hf' : ∀ s, WellFormed d2 s →
            WellFormed d2 (f s) ∧
              evalTrie val (2 ^ d1 * (2 * step)) ((base + step) + (2 * step) * (idx / 2)) (f s) =
                evalTrie val (2 ^ d1 * (2 * step)) ((base + step) + (2 * step) * (idx / 2)) s + delta := by
          rw [hstep_eq, hbase_eq]; exact hf
        obtain ⟨hwfR, hevR⟩ := ih (idx / 2) (2 * step) (base + step) hi hidx' hwfHi hf'
        refine ⟨?_, ?_⟩
        · rw [hadd_eq]; exact ⟨hwfLo, hwfR⟩
        · simp only [evalTrie, hevR]; ring

lemma wellFormed_and_eval_addAt (val : ℕ → ℝ) (depth idx step base : ℕ) (delta : ℤ) (t : IntTrie)
    (hidx : idx < 2 ^ depth) (hwf : WellFormed depth t) :
    WellFormed depth (addAt depth idx delta t) ∧
      evalTrie val step base (addAt depth idx delta t) =
        evalTrie val step base t + (delta : ℝ) * val (base + step * idx) := by
  unfold addAt
  by_cases hd : delta = 0
  · subst hd; simp [hwf]
  · have hbeq : (delta == 0) = false := by simp [hd]
    rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
    have h := wellFormed_and_eval_modifyAt val depth 0 idx step base
      ((delta : ℝ) * val (base + step * idx)) (addLeaf delta) t hidx (by simpa using hwf)
      (fun s hs => wellFormed_and_eval_addLeaf val (2 ^ depth * step) (base + step * idx) delta s hs)
    simpa using h

end IntTrie

/-! ### Part 3: Engine 1 — `BinomialBasisLP` (Subset-`J` Terwilliger LP & Farkas Checker) -/

/-- Constraint step in a pure-integer Subset-`J` binomial-basis Terwilliger LP certificate. -/
inductive BinoStep where
  | eqP0 (μ : ℤ)
  | eqP1 (μ : ℤ)
  | eqPFix (k v : ℕ) (μ : ℤ)
  | eqDiag (j : ℕ) (μ : ℤ)
  | eqB00 (j : ℕ) (μ : ℤ)
  | eqB10 (j : ℕ) (μ : ℤ)
  | eqB01 (j : ℕ) (μ : ℤ)
  | eqSym (i j t : ℕ) (μ : ℤ)
  | ubPLo (k : ℕ) (lam : ℕ)
  | ubPHi (k : ℕ) (lam : ℕ)
  | ubHGe0 (j a b : ℕ) (lam : ℕ)
  | ubHLePi (j a b : ℕ) (lam : ℕ)
  | ubHLePj (j a b : ℕ) (lam : ℕ)
  | ubHMcc (j a b : ℕ) (lam : ℕ)
  deriving Repr, DecidableEq

/-- Tail-recursive addition of `scale * p(k)` into a depth-4 `uTrie`. -/
def addEvalPLoop (k : ℕ) (scale : ℤ) : ℕ → ℕ → ℕ → IntTrie → IntTrie
  | 0, _, _, t => t
  | rem + 1, r, cur, t =>
      let t' := IntTrie.addAt 4 r (scale * (cur : ℤ)) t
      addEvalPLoop k scale rem (r + 1) (cur * (k - r) / (r + 1)) t'

/-- Add `scale * eval_p(k)` into the depth-4 univariate basis trie `uTrie`. -/
def addEvalP (d k : ℕ) (scale : ℤ) (t : IntTrie) : IntTrie :=
  if scale == 0 then t
  else addEvalPLoop k scale (min d k + 1) 0 1 t

/-- Inner `s`-loop of `addEvalH` into a depth-4 trie for fixed `(j, r)`. -/
def addEvalHRow (b : ℕ) (scaleCar : ℤ) : ℕ → ℕ → ℕ → IntTrie → IntTrie
  | 0, _, _, t => t
  | rem + 1, s, curS, t =>
      let t' := IntTrie.addAt 4 s (scaleCar * (curS : ℤ)) t
      addEvalHRow b scaleCar rem (s + 1) (curS * (b - s) / (s + 1)) t'

/-- Outer `r`-loop of `addEvalH` into a depth-8 trie for fixed `j`. -/
def addEvalHOuter (n d j a b : ℕ) (scale : ℤ) : ℕ → ℕ → ℕ → IntTrie → IntTrie
  | 0, _, _, t => t
  | rem + 1, r, curR, t =>
      let sMax := min (d - r) (min (n - j) b)
      let t' := IntTrie.modifyAt 4 r (addEvalHRow b (scale * (curR : ℤ)) (sMax + 1) 0 1) t
      addEvalHOuter n d j a b scale rem (r + 1) (curR * (a - r) / (r + 1)) t'

/-- Add `scale * eval_h(j, a, b)` into the depth-14 bivariate basis trie `cTrie`. -/
def addEvalH (n d j a b : ℕ) (scale : ℤ) (t : IntTrie) : IntTrie :=
  if scale == 0 then t
  else
    let rMax := min d (min j a)
    IntTrie.modifyAt 6 j (addEvalHOuter n d j a b scale (rMax + 1) 0 1) t

/-- Side-condition check for a single `BinoStep`. -/
def binoStepOk (n : ℕ) (extraFix : List (ℕ × ℕ)) : BinoStep → Bool
  | .eqP0 _ => true
  | .eqP1 _ => decide (1 ≤ n)
  | .eqPFix k v _ => decide (k ≤ n) && extraFix.contains (k, v)
  | .eqDiag j _ => decide (j ≤ n)
  | .eqB00 j _ => decide (j ≤ n)
  | .eqB10 j _ => decide (1 ≤ j) && decide (j ≤ n)
  | .eqB01 j _ => decide (j + 1 ≤ n)
  | .eqSym i j t _ =>
      decide (i ≤ n) && decide (j ≤ n) && decide (t ≤ i) && decide (t ≤ j) && decide (i + j ≤ n + t)
  | .ubPLo k _ => decide (k ≤ n)
  | .ubPHi k _ => decide (k ≤ n)
  | .ubHGe0 j a b _ => decide (j ≤ n) && decide (a ≤ j) && decide (b ≤ n - j)
  | .ubHLePi j a b _ => decide (j ≤ n) && decide (a ≤ j) && decide (b ≤ n - j)
  | .ubHLePj j a b _ => decide (j ≤ n) && decide (a ≤ j) && decide (b ≤ n - j)
  | .ubHMcc j a b _ => decide (j ≤ n) && decide (a ≤ j) && decide (b ≤ n - j)

/-- Univariate `uTrie` contribution of a single `BinoStep`. -/
def binoStepU (d : ℕ) : BinoStep → IntTrie
  | .eqP0 μ => addEvalP d 0 μ .empty
  | .eqP1 μ => addEvalP d 1 μ .empty
  | .eqPFix k _ μ => addEvalP d k μ .empty
  | .eqDiag j μ => addEvalP d j (-μ) .empty
  | .eqB00 _ _ => .empty
  | .eqB10 j μ => addEvalP d j (-μ) .empty
  | .eqB01 j μ => addEvalP d j (-μ) .empty
  | .eqSym _ _ _ _ => .empty
  | .ubPLo k lam => addEvalP d k (lam : ℤ) .empty
  | .ubPHi k lam => addEvalP d k (-(lam : ℤ)) .empty
  | .ubHGe0 _ _ _ _ => .empty
  | .ubHLePi _ a b lam => addEvalP d (a + b) (lam : ℤ) .empty
  | .ubHLePj j _ _ lam => addEvalP d j (lam : ℤ) .empty
  | .ubHMcc j a b lam => addEvalP d j (-(lam : ℤ)) (addEvalP d (a + b) (-(lam : ℤ)) .empty)

/-- Bivariate `cTrie` contribution of a single `BinoStep`. -/
def binoStepC (n d : ℕ) : BinoStep → IntTrie
  | .eqP0 _ => .empty
  | .eqP1 _ => .empty
  | .eqPFix _ _ _ => .empty
  | .eqDiag j μ => addEvalH n d j j 0 μ .empty
  | .eqB00 j μ => addEvalH n d j 0 0 μ .empty
  | .eqB10 j μ => addEvalH n d j 1 0 μ .empty
  | .eqB01 j μ => addEvalH n d j 0 1 μ .empty
  | .eqSym i j t μ => addEvalH n d i t (j - t) (-μ) (addEvalH n d j t (i - t) μ .empty)
  | .ubPLo _ _ => .empty
  | .ubPHi _ _ => .empty
  | .ubHGe0 j a b lam => addEvalH n d j a b (lam : ℤ) .empty
  | .ubHLePi j a b lam => addEvalH n d j a b (-(lam : ℤ)) .empty
  | .ubHLePj j a b lam => addEvalH n d j a b (-(lam : ℤ)) .empty
  | .ubHMcc j a b lam => addEvalH n d j a b (lam : ℤ) .empty

/-- Dual-objective contribution of a single `BinoStep`. -/
def binoStepObj : BinoStep → ℤ
  | .eqP0 _ => 0
  | .eqP1 μ => μ
  | .eqPFix _ v μ => μ * (v : ℤ)
  | .eqDiag _ _ => 0
  | .eqB00 _ _ => 0
  | .eqB10 _ _ => 0
  | .eqB01 _ _ => 0
  | .eqSym _ _ _ _ => 0
  | .ubPLo _ _ => 0
  | .ubPHi _ lam => -(lam : ℤ)
  | .ubHGe0 _ _ _ _ => 0
  | .ubHLePi _ _ _ _ => 0
  | .ubHLePj _ _ _ _ => 0
  | .ubHMcc _ _ _ lam => -(lam : ℤ)

/-- Pure-integer Farkas infeasibility checker for the Subset-`J` Terwilliger LP. -/
def checkBinoFarkas (n d : ℕ) (tree : BinTree BinoStep) : Bool :=
  decide (n < 64) && decide (d < 16) &&
    tree.all (binoStepOk n []) &&
    (IntTrie.mergeTree (binoStepU d) tree).isZero &&
    (IntTrie.mergeTree (binoStepC n d) tree).isZero &&
    decide (0 < tree.sumZ binoStepObj)

/-- Pure-integer LP bound checker proving `(objScale : ℝ) * (objSign : ℝ) * p(objK) ≥ expectedLb`. -/
def checkBinoBound (n d : ℕ) (extraFix : List (ℕ × ℕ)) (tree : BinTree BinoStep)
    (objK : ℕ) (objSign : ℤ) (objScale : ℕ) (expectedLb : ℤ) : Bool :=
  decide (n < 64) && decide (d < 16) && decide (objK ≤ n) &&
    tree.all (binoStepOk n extraFix) &&
    (addEvalP d objK (-(objScale : ℤ) * objSign) (IntTrie.mergeTree (binoStepU d) tree)).isZero &&
    (IntTrie.mergeTree (binoStepC n d) tree).isZero &&
    decide (expectedLb ≤ tree.sumZ binoStepObj)

/-! #### Soundness of `BinomialBasisLP` -/

private lemma wellFormed_and_eval_addEvalPLoop (uVal : ℕ → ℝ) (k : ℕ) (scale : ℤ) :
    ∀ rem r cur t,
      r + rem ≤ 16 → cur = Nat.choose k r → IntTrie.WellFormed 4 t →
      IntTrie.WellFormed 4 (addEvalPLoop k scale rem r cur t) ∧
        IntTrie.evalTrie uVal 1 0 (addEvalPLoop k scale rem r cur t) =
          IntTrie.evalTrie uVal 1 0 t +
            (scale : ℝ) * ∑ m ∈ Finset.range rem, uVal (r + m) * (Nat.choose k (r + m) : ℝ)
  | 0, _, _, t, _, _, hwf => by simp [addEvalPLoop, hwf]
  | rem + 1, r, cur, t, hlt, hcur, hwf => by
    simp only [addEvalPLoop]
    have hr16 : r < 2 ^ 4 := by omega
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_addAt uVal 4 r 1 0 (scale * (cur : ℤ)) t hr16 hwf
    have hnext : cur * (k - r) / (r + 1) = Nat.choose k (r + 1) := by
      rw [hcur]; exact choose_step_div k r
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addEvalPLoop uVal k scale rem (r + 1)
      (cur * (k - r) / (r + 1)) (IntTrie.addAt 4 r (scale * (cur : ℤ)) t) (by omega) hnext hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1, Finset.sum_range_succ', hcur]
    have hshift : ∑ m ∈ Finset.range rem, uVal (r + 1 + m) * (Nat.choose k (r + 1 + m) : ℝ) =
        ∑ m ∈ Finset.range rem, uVal (r + (m + 1)) * (Nat.choose k (r + (m + 1)) : ℝ) := by
      apply Finset.sum_congr rfl; intro m _
      have : r + 1 + m = r + (m + 1) := by omega
      rw [this]
    rw [hshift]
    simp only [zero_add, one_mul, Nat.add_zero]
    push_cast; ring

private lemma wellFormed_and_eval_addEvalP (uVal : ℕ → ℝ) (d k : ℕ) (scale : ℤ) (t : IntTrie)
    (hd : d < 16) (hwf : IntTrie.WellFormed 4 t) :
    IntTrie.WellFormed 4 (addEvalP d k scale t) ∧
      IntTrie.evalTrie uVal 1 0 (addEvalP d k scale t) =
        IntTrie.evalTrie uVal 1 0 t +
          (scale : ℝ) * ∑ r ∈ Finset.range (d + 1), uVal r * (Nat.choose k r : ℝ) := by
  unfold addEvalP
  by_cases hs : scale = 0
  · subst hs; simp [hwf]
  · have hbeq : (scale == 0) = false := by simp [hs]
    rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hwf', hev'⟩ := wellFormed_and_eval_addEvalPLoop uVal k scale (min d k + 1) 0 1 t
      (by omega) (by simp) hwf
    refine ⟨hwf', ?_⟩
    rw [hev']
    congr 2
    have hsub : Finset.range (min d k + 1) ⊆ Finset.range (d + 1) :=
      Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl; intro r _; simp
    · intro r hr hnot
      have hrk : k < r := by
        simp only [Finset.mem_range] at hr hnot; omega
      simp [Nat.choose_eq_zero_of_lt hrk]

private lemma wellFormed_and_eval_addEvalHRow (cVal : ℕ → ℝ) (step base b : ℕ) (scaleCar : ℤ) :
    ∀ rem s curS t,
      s + rem ≤ 16 → curS = Nat.choose b s → IntTrie.WellFormed 4 t →
      IntTrie.WellFormed 4 (addEvalHRow b scaleCar rem s curS t) ∧
        IntTrie.evalTrie cVal step base (addEvalHRow b scaleCar rem s curS t) =
          IntTrie.evalTrie cVal step base t +
            (scaleCar : ℝ) *
              ∑ m ∈ Finset.range rem, cVal (base + step * (s + m)) * (Nat.choose b (s + m) : ℝ)
  | 0, _, _, t, _, _, hwf => by simp [addEvalHRow, hwf]
  | rem + 1, s, curS, t, hlt, hcur, hwf => by
    simp only [addEvalHRow]
    have hs16 : s < 2 ^ 4 := by omega
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_addAt cVal 4 s step base
      (scaleCar * (curS : ℤ)) t hs16 hwf
    have hnext : curS * (b - s) / (s + 1) = Nat.choose b (s + 1) := by
      rw [hcur]; exact choose_step_div b s
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addEvalHRow cVal step base b scaleCar rem (s + 1)
      (curS * (b - s) / (s + 1)) (IntTrie.addAt 4 s (scaleCar * (curS : ℤ)) t) (by omega) hnext hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1, Finset.sum_range_succ', hcur]
    have hshift : ∑ m ∈ Finset.range rem,
        cVal (base + step * (s + 1 + m)) * (Nat.choose b (s + 1 + m) : ℝ) =
        ∑ m ∈ Finset.range rem,
          cVal (base + step * (s + (m + 1))) * (Nat.choose b (s + (m + 1)) : ℝ) := by
      apply Finset.sum_congr rfl; intro m _
      have : s + 1 + m = s + (m + 1) := by omega
      rw [this]
    rw [hshift]
    simp only [Nat.add_zero]
    push_cast; ring

lemma wellFormed_and_eval_addEvalHOuter (cVal : ℕ → ℝ) (n d j a b step base : ℕ)
    (scale : ℤ) (hd : d < 16) (hb : b ≤ n - j) :
    ∀ rem r curR t,
      r + rem ≤ d + 1 → curR = Nat.choose a r → IntTrie.WellFormed 8 t →
      IntTrie.WellFormed 8 (addEvalHOuter n d j a b scale rem r curR t) ∧
        IntTrie.evalTrie cVal step base (addEvalHOuter n d j a b scale rem r curR t) =
          IntTrie.evalTrie cVal step base t +
            (scale : ℝ) *
              ∑ m ∈ Finset.range rem,
                ∑ s ∈ Finset.range (d + 1 - (r + m)),
                  cVal (base + step * (r + m) + (16 * step) * s) *
                    (Nat.choose a (r + m) : ℝ) * (Nat.choose b s : ℝ)
  | 0, _, _, t, _, _, hwf => by simp [addEvalHOuter, hwf]
  | rem + 1, r, curR, t, hlt, hcur, hwf => by
    simp only [addEvalHOuter]
    set sMax := min (d - r) (min (n - j) b)
    have hr16 : r < 2 ^ 4 := by omega
    have hwf44 : IntTrie.WellFormed (4 + 4) t := hwf
    have hrow : ∀ s, IntTrie.WellFormed 4 s →
        IntTrie.WellFormed 4 (addEvalHRow b (scale * (curR : ℤ)) (sMax + 1) 0 1 s) ∧
          IntTrie.evalTrie cVal (2 ^ 4 * step) (base + step * r)
              (addEvalHRow b (scale * (curR : ℤ)) (sMax + 1) 0 1 s) =
            IntTrie.evalTrie cVal (2 ^ 4 * step) (base + step * r) s +
              (scale : ℝ) *
                ∑ sv ∈ Finset.range (d + 1 - r),
                  cVal (base + step * r + (16 * step) * sv) *
                    (Nat.choose a r : ℝ) * (Nat.choose b sv : ℝ) := by
      intro s hs
      obtain ⟨hwfS, hevS⟩ := wellFormed_and_eval_addEvalHRow cVal (2 ^ 4 * step) (base + step * r) b
        (scale * (curR : ℤ)) (sMax + 1) 0 1 s (by omega) (by simp) hs
      refine ⟨hwfS, ?_⟩
      rw [hevS, hcur]
      congr 1
      have hsub : Finset.range (sMax + 1) ⊆ Finset.range (d + 1 - r) :=
        Finset.range_mono (by omega)
      rw [← Finset.sum_subset hsub]
      · rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro sv _
        have hpow16 : (2 ^ 4 : ℕ) * step = 16 * step := by ring
        simp only [zero_add, hpow16]
        push_cast; ring
      · intro sv hsv hnot
        have hsb : b < sv := by
          simp only [Finset.mem_range] at hsv hnot; omega
        simp [Nat.choose_eq_zero_of_lt hsb]
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_modifyAt cVal 4 4 r step base
      ((scale : ℝ) * ∑ sv ∈ Finset.range (d + 1 - r),
        cVal (base + step * r + (16 * step) * sv) * (Nat.choose a r : ℝ) * (Nat.choose b sv : ℝ))
      (addEvalHRow b (scale * (curR : ℤ)) (sMax + 1) 0 1) t hr16 hwf44 hrow
    have hnext : curR * (a - r) / (r + 1) = Nat.choose a (r + 1) := by
      rw [hcur]; exact choose_step_div a r
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addEvalHOuter cVal n d j a b step base scale hd hb
      rem (r + 1) (curR * (a - r) / (r + 1)) _ (by omega) hnext hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1, Finset.sum_range_succ']
    have hshift :
        ∑ m ∈ Finset.range rem, ∑ s ∈ Finset.range (d + 1 - (r + 1 + m)),
          cVal (base + step * (r + 1 + m) + 16 * step * s) *
            (Nat.choose a (r + 1 + m) : ℝ) * (Nat.choose b s : ℝ) =
        ∑ m ∈ Finset.range rem, ∑ s ∈ Finset.range (d + 1 - (r + (m + 1))),
          cVal (base + step * (r + (m + 1)) + 16 * step * s) *
            (Nat.choose a (r + (m + 1)) : ℝ) * (Nat.choose b s : ℝ) := by
      apply Finset.sum_congr rfl; intro m _
      have : r + 1 + m = r + (m + 1) := by omega
      rw [this]
    rw [hshift]
    simp only [Nat.add_zero]
    ring

lemma wellFormed_and_eval_addEvalH (cCoeff : ℕ → ℕ → ℕ → ℝ) (n d j a b : ℕ) (scale : ℤ)
    (t : IntTrie) (hn : n < 64) (hd : d < 16) (hj : j ≤ n) (ha : a ≤ j) (hb : b ≤ n - j)
    (hwf : IntTrie.WellFormed 14 t) :
    let cVal : ℕ → ℝ := fun idx => cCoeff (idx % 64) ((idx / 64) % 16) (idx / 1024)
    IntTrie.WellFormed 14 (addEvalH n d j a b scale t) ∧
      IntTrie.evalTrie cVal 1 0 (addEvalH n d j a b scale t) =
        IntTrie.evalTrie cVal 1 0 t +
          (scale : ℝ) *
            ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
              cCoeff j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) := by
  intro cVal
  unfold addEvalH
  by_cases hs : scale = 0
  · subst hs; simp [hwf]
  · have hbeq : (scale == 0) = false := by simp [hs]
    rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
    set rMax := min d (min j a)
    have hj64 : j < 2 ^ 6 := by omega
    have hwf68 : IntTrie.WellFormed (6 + 8) t := hwf
    have houter : ∀ s, IntTrie.WellFormed 8 s →
        IntTrie.WellFormed 8 (addEvalHOuter n d j a b scale (rMax + 1) 0 1 s) ∧
          IntTrie.evalTrie cVal (2 ^ 6 * 1) (0 + 1 * j)
              (addEvalHOuter n d j a b scale (rMax + 1) 0 1 s) =
            IntTrie.evalTrie cVal (2 ^ 6 * 1) (0 + 1 * j) s +
              (scale : ℝ) *
                ∑ r ∈ Finset.range (d + 1), ∑ sv ∈ Finset.range (d + 1 - r),
                  cCoeff j r sv * (Nat.choose a r : ℝ) * (Nat.choose b sv : ℝ) := by
      intro s hs
      obtain ⟨hwfO, hevO⟩ := wellFormed_and_eval_addEvalHOuter cVal n d j a b (2 ^ 6 * 1) (0 + 1 * j)
        scale hd hb (rMax + 1) 0 1 s (by omega) (by simp) hs
      refine ⟨hwfO, ?_⟩
      rw [hevO]
      congr 2
      have hsub : Finset.range (rMax + 1) ⊆ Finset.range (d + 1) :=
        Finset.range_mono (by omega)
      rw [← Finset.sum_subset hsub]
      · apply Finset.sum_congr rfl; intro r hr
        have hr16 : r < 16 := by simp only [Finset.mem_range] at hr; omega
        simp only [zero_add, one_mul, mul_one]
        apply Finset.sum_congr rfl; intro sv hsv
        have hsv16 : sv < 16 := by simp only [Finset.mem_range] at hsv; omega
        have hidx_j : (j + 2 ^ 6 * r + 16 * 2 ^ 6 * sv) % 64 = j := by omega
        have hidx_r : ((j + 2 ^ 6 * r + 16 * 2 ^ 6 * sv) / 64) % 16 = r := by omega
        have hidx_s : (j + 2 ^ 6 * r + 16 * 2 ^ 6 * sv) / 1024 = sv := by omega
        simp only [cVal, hidx_j, hidx_r, hidx_s]
      · intro r hr hnot
        have hra : a < r := by
          simp only [Finset.mem_range] at hr hnot; omega
        apply Finset.sum_eq_zero; intro sv _
        simp [Nat.choose_eq_zero_of_lt hra]
    exact IntTrie.wellFormed_and_eval_modifyAt cVal 6 8 j 1 0 _ _ t hj64 hwf68 houter

/-- Single-step soundness for `BinomialBasisLP`. -/
private lemma binoStep_sound {n d : ℕ} (f : BooleanFun n)
    (hn : n < 64) (hd : d < 16)
    (hf0 : f (zeroVec n) = false)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true)
    (extraFix : List (ℕ × ℕ))
    (hextra : ∀ p ∈ extraFix, layerAvg (fun x => boolToReal (f x)) p.1 = (p.2 : ℝ))
    (u : ℕ → ℝ)
    (hu : ∀ k ≤ n, layerAvg (fun x => boolToReal (f x)) k =
      ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose k r : ℝ))
    (c : ℕ → ℕ → ℕ → ℝ)
    (hc : ∀ j ≤ n, ∀ a b, a ≤ j → b ≤ n - j →
      pairCorr f (a + b) j a =
        ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ))
    (step : BinoStep) (hok : binoStepOk n extraFix step = true) :
    let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
    IntTrie.WellFormed 4 (binoStepU d step) ∧
      IntTrie.WellFormed 14 (binoStepC n d step) ∧
      (binoStepObj step : ℝ) ≤
        IntTrie.evalTrie u 1 0 (binoStepU d step) +
        IntTrie.evalTrie cVal 1 0 (binoStepC n d step) := by
  intro cVal
  cases step with
  | eqP0 μ =>
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d 0 μ .empty hd trivial
    have hp0 : ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose 0 r : ℝ) = 0 := by
      rw [← hu 0 (Nat.zero_le n)]; exact layerAvg_bool_zero hf0
    refine ⟨hwfU, trivial, ?_⟩
    simp only [binoStepObj, binoStepU, binoStepC, hevU, hp0, IntTrie.evalTrie]; norm_num
  | eqP1 μ =>
    simp only [binoStepOk, decide_eq_true_eq] at hok
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d 1 μ .empty hd trivial
    have hp1 : ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose 1 r : ℝ) = 1 := by
      rw [← hu 1 hok]; exact layerAvg_bool_one (by omega) hf1
    refine ⟨hwfU, trivial, ?_⟩
    simp only [binoStepObj, binoStepU, binoStepC, hevU, hp1, IntTrie.evalTrie]; linarith
  | eqPFix k v μ =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem] at hok
    obtain ⟨hkn, hmem⟩ := hok
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d k μ .empty hd trivial
    have hpk : ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose k r : ℝ) = (v : ℝ) := by
      rw [← hu k hkn]; exact hextra (k, v) hmem
    refine ⟨hwfU, trivial, ?_⟩
    simp only [binoStepObj, binoStepU, binoStepC, hevU, hpk, IntTrie.evalTrie]; push_cast; linarith
  | eqDiag j μ =>
    simp only [binoStepOk, decide_eq_true_eq] at hok
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d j (-μ) .empty hd trivial
    obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalH c n d j j 0 μ .empty hn hd hok (le_refl j)
      (Nat.zero_le _) trivial
    have heq : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose j r : ℝ) * (Nat.choose 0 s : ℝ) =
        ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose j r : ℝ) := by
      rw [← hc j hok j 0 (le_refl j) (Nat.zero_le _), ← hu j hok, Nat.add_zero]
      exact pairCorr_diag f hok
    refine ⟨hwfU, hwfC, ?_⟩
    dsimp only [binoStepObj, binoStepU, binoStepC]
    rw [hevU, hevC, heq]; simp only [IntTrie.evalTrie]; push_cast; linarith
  | eqB00 j μ =>
    simp only [binoStepOk, decide_eq_true_eq] at hok
    obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalH c n d j 0 0 μ .empty hn hd hok
      (Nat.zero_le j) (Nat.zero_le _) trivial
    have heq : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose 0 r : ℝ) * (Nat.choose 0 s : ℝ) = 0 := by
      rw [← hc j hok 0 0 (Nat.zero_le j) (Nat.zero_le _), Nat.add_zero]
      exact pairCorr_zero_left f hf0
    refine ⟨trivial, hwfC, ?_⟩
    dsimp only [binoStepObj, binoStepU, binoStepC]
    rw [hevC, heq]; simp only [IntTrie.evalTrie]; norm_num
  | eqB10 j μ =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj1, hjn⟩ := hok
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d j (-μ) .empty hd trivial
    obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalH c n d j 1 0 μ .empty hn hd hjn hj1
      (Nat.zero_le _) trivial
    have heq : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose 1 r : ℝ) * (Nat.choose 0 s : ℝ) =
        ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose j r : ℝ) := by
      rw [← hc j hjn 1 0 hj1 (Nat.zero_le _), ← hu j hjn, Nat.add_zero]
      exact pairCorr_one_left_one f hj1 hjn hf1
    refine ⟨hwfU, hwfC, ?_⟩
    dsimp only [binoStepObj, binoStepU, binoStepC]
    rw [hevU, hevC, heq]; simp only [IntTrie.evalTrie]; push_cast; linarith
  | eqB01 j μ =>
    simp only [binoStepOk, decide_eq_true_eq] at hok
    have hjn : j ≤ n := by omega
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d j (-μ) .empty hd trivial
    obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalH c n d j 0 1 μ .empty hn hd hjn
      (Nat.zero_le j) (by omega) trivial
    have heq : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose 0 r : ℝ) * (Nat.choose 1 s : ℝ) =
        ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose j r : ℝ) := by
      rw [← hc j hjn 0 1 (Nat.zero_le j) (by omega), ← hu j hjn, Nat.zero_add]
      exact pairCorr_one_left_zero f hok hf1
    refine ⟨hwfU, hwfC, ?_⟩
    dsimp only [binoStepObj, binoStepU, binoStepC]
    rw [hevU, hevC, heq]; simp only [IntTrie.evalTrie]; push_cast; linarith
  | eqSym i j t μ =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hin, hjn⟩, hti⟩, htj⟩, hij⟩ := hok
    have hvalid : ValidTriple n i j t := ⟨hin, hjn, hti, htj, hij⟩
    obtain ⟨hwfC1, hevC1⟩ := wellFormed_and_eval_addEvalH c n d j t (i - t) μ .empty hn hd hjn
      htj (by omega) trivial
    obtain ⟨hwfC2, hevC2⟩ := wellFormed_and_eval_addEvalH c n d i t (j - t) (-μ) _ hn hd hin
      hti (by omega) hwfC1
    have h1 : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
        c j r s * (Nat.choose t r : ℝ) * (Nat.choose (i - t) s : ℝ) = pairCorr f i j t := by
      rw [← hc j hjn t (i - t) htj (by omega), Nat.add_sub_of_le hti]
    have h2 : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
        c i r s * (Nat.choose t r : ℝ) * (Nat.choose (j - t) s : ℝ) = pairCorr f j i t := by
      rw [← hc i hin t (j - t) hti (by omega), Nat.add_sub_of_le htj]
    refine ⟨trivial, hwfC2, ?_⟩
    dsimp only [binoStepObj, binoStepU, binoStepC]
    rw [hevC2, hevC1, h1, h2, pairCorr_symm f hvalid]; simp only [IntTrie.evalTrie]
    push_cast; linarith
  | ubPLo k lam =>
    simp only [binoStepOk, decide_eq_true_eq] at hok
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d k (lam : ℤ) .empty hd trivial
    have hnn : 0 ≤ ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose k r : ℝ) := by
      rw [← hu k hok]; exact layerAvg_bool_nonneg f k
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfU, trivial, ?_⟩
    simp only [binoStepObj, binoStepU, binoStepC, hevU, IntTrie.evalTrie]; push_cast; nlinarith
  | ubPHi k lam =>
    simp only [binoStepOk, decide_eq_true_eq] at hok
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d k (-(lam : ℤ)) .empty hd trivial
    have hle1 : ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose k r : ℝ) ≤ 1 := by
      rw [← hu k hok]; exact layerAvg_bool_le_one f k hok
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfU, trivial, ?_⟩
    simp only [binoStepObj, binoStepU, binoStepC, hevU, IntTrie.evalTrie]; push_cast; nlinarith
  | ubHGe0 j a b lam =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hjn, haj⟩, hbnj⟩ := hok
    obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalH c n d j a b (lam : ℤ) .empty hn hd hjn
      haj hbnj trivial
    have hnn : 0 ≤ ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
        c j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) := by
      rw [← hc j hjn a b haj hbnj]; exact pairCorr_nonneg f
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨trivial, hwfC, ?_⟩
    dsimp only [binoStepObj, binoStepU, binoStepC]
    rw [hevC]; simp only [IntTrie.evalTrie]; push_cast; nlinarith
  | ubHLePi j a b lam =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hjn, haj⟩, hbnj⟩ := hok
    have hab : a + b ≤ n := by omega
    have hvalid : ValidTriple n (a + b) j a := ⟨hab, hjn, Nat.le_add_right a b, haj, by omega⟩
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d (a + b) (lam : ℤ) .empty hd trivial
    obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalH c n d j a b (-(lam : ℤ)) .empty hn hd
      hjn haj hbnj trivial
    have hle_pi : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) ≤
        ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose (a + b) r : ℝ) := by
      rw [← hc j hjn a b haj hbnj, ← hu (a + b) hab]
      exact pairCorr_le_left f hvalid
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfU, hwfC, ?_⟩
    dsimp only [binoStepObj, binoStepU, binoStepC]
    rw [hevU, hevC]; simp only [IntTrie.evalTrie]; push_cast; nlinarith
  | ubHLePj j a b lam =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hjn, haj⟩, hbnj⟩ := hok
    have hab : a + b ≤ n := by omega
    have hvalid : ValidTriple n (a + b) j a := ⟨hab, hjn, Nat.le_add_right a b, haj, by omega⟩
    obtain ⟨hwfU, hevU⟩ := wellFormed_and_eval_addEvalP u d j (lam : ℤ) .empty hd trivial
    obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalH c n d j a b (-(lam : ℤ)) .empty hn hd
      hjn haj hbnj trivial
    have hle_pj : ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) ≤
        ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose j r : ℝ) := by
      rw [← hc j hjn a b haj hbnj, ← hu j hjn]
      exact pairCorr_le_right f hvalid
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfU, hwfC, ?_⟩
    dsimp only [binoStepObj, binoStepU, binoStepC]
    rw [hevU, hevC]; simp only [IntTrie.evalTrie]; push_cast; nlinarith
  | ubHMcc j a b lam =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hjn, haj⟩, hbnj⟩ := hok
    have hab : a + b ≤ n := by omega
    have hvalid : ValidTriple n (a + b) j a := ⟨hab, hjn, Nat.le_add_right a b, haj, by omega⟩
    obtain ⟨hwfU1, hevU1⟩ := wellFormed_and_eval_addEvalP u d (a + b) (-(lam : ℤ)) .empty hd trivial
    obtain ⟨hwfU2, hevU2⟩ := wellFormed_and_eval_addEvalP u d j (-(lam : ℤ)) _ hd hwfU1
    obtain ⟨hwfC, hevC⟩ := wellFormed_and_eval_addEvalH c n d j a b (lam : ℤ) .empty hn hd
      hjn haj hbnj trivial
    have hmcc : ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose (a + b) r : ℝ) +
        ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose j r : ℝ) -
        ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) ≤ 1 := by
      rw [← hc j hjn a b haj hbnj, ← hu (a + b) hab, ← hu j hjn]
      exact pairCorr_frechet f hvalid
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfU2, hwfC, ?_⟩
    dsimp only [binoStepObj, binoStepU, binoStepC]
    rw [hevU2, hevU1, hevC]; simp only [IntTrie.evalTrie]
    push_cast; nlinarith

private lemma binoTree_sound {n d : ℕ} (f : BooleanFun n)
    (hn : n < 64) (hd : d < 16)
    (hf : polyDegree f ≤ d)
    (hf0 : f (zeroVec n) = false)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true)
    (extraFix : List (ℕ × ℕ))
    (hextra : ∀ p ∈ extraFix, layerAvg (fun x => boolToReal (f x)) p.1 = (p.2 : ℝ))
    (tree : BinTree BinoStep)
    (hok : tree.all (binoStepOk n extraFix) = true) :
    ∃ (u : ℕ → ℝ) (c : ℕ → ℕ → ℕ → ℝ),
      (∀ k ≤ n, layerAvg (fun x => boolToReal (f x)) k =
        ∑ r ∈ Finset.range (d + 1), u r * (Nat.choose k r : ℝ)) ∧
      IntTrie.WellFormed 4 (IntTrie.mergeTree (binoStepU d) tree) ∧
      IntTrie.WellFormed 14 (IntTrie.mergeTree (binoStepC n d) tree) ∧
      (tree.sumZ binoStepObj : ℝ) ≤
        IntTrie.evalTrie u 1 0 (IntTrie.mergeTree (binoStepU d) tree) +
        IntTrie.evalTrie (fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)) 1 0
          (IntTrie.mergeTree (binoStepC n d) tree) := by
  have hrep : ∀ x : Fin n → Bool,
      ∑ S ∈ (supportOf x).powerset, (mobiusCoeff f S : ℝ) = boolToReal (f x) := by
    intro x
    have h := representsPoly_mobius f x
    change MvPolynomial.eval (fun i => boolToReal (x i))
      (multilinearPoly (fun S => (mobiusCoeff f S : ℝ))) = boolToReal (f x) at h
    rwa [eval_multilinearPoly] at h
  have hdeg : ∀ S : Finset (Fin n), d < S.card → (mobiusCoeff f S : ℝ) = 0 := by
    intro S hS; simp [mobiusCoeff_eq_zero_of_polyDegree_lt (lt_of_le_of_lt hf hS)]
  obtain ⟨u, hu⟩ := layerAvg_eq_binomial_sum (fun x => boolToReal (f x))
    (fun S => (mobiusCoeff f S : ℝ)) hrep hdeg
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
  refine ⟨u, c, hu, ?_⟩
  let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
  induction tree with
  | empty =>
    exact ⟨trivial, trivial, by simp [BinTree.sumZ, IntTrie.mergeTree, IntTrie.evalTrie]⟩
  | leaf s =>
    exact binoStep_sound f hn hd hf0 hf1 extraFix hextra u hu c hc s hok
  | node l r ihl ihr =>
    simp only [BinTree.all, Bool.and_eq_true] at hok
    obtain ⟨hwfUl, hwfCl, hlel⟩ := ihl hok.1
    obtain ⟨hwfUr, hwfCr, hler⟩ := ihr hok.2
    obtain ⟨hwfU, hevU⟩ := IntTrie.wellFormed_and_eval_merge u 4 1 0 _ _ hwfUl hwfUr
    obtain ⟨hwfC, hevC⟩ := IntTrie.wellFormed_and_eval_merge cVal 14 1 0 _ _ hwfCl hwfCr
    refine ⟨hwfU, hwfC, ?_⟩
    dsimp only [BinTree.sumZ, IntTrie.mergeTree]
    rw [hevU, hevC]; push_cast; linarith

/-- **Soundness of Subset-`J` Farkas Infeasibility Checker**:
A verified pure-integer `BinTree` certificate proves `maxSensitivity f < n` for EVERY Boolean
function `f` in ANY dimension `m` with `polyDegree f ≤ d`. -/
theorem maxSensitivity_lt_of_bino_farkas {n d : ℕ} (tree : BinTree BinoStep)
    (hcert : checkBinoFarkas n d tree = true) :
    ∀ {m : ℕ} (f : BooleanFun m), polyDegree f ≤ d → maxSensitivity f < n := by
  unfold checkBinoFarkas at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcert
  obtain ⟨⟨⟨⟨⟨hn, hd⟩, hok⟩, hu0⟩, hc0⟩, hpos⟩ := hcert
  apply maxSensitivity_lt_of_no_normalized
  rintro ⟨f, hdeg, hf0, hf1⟩
  obtain ⟨u, c, _, _, _, hle⟩ := binoTree_sound f hn hd hdeg hf0 hf1 [] (by simp) tree hok
  rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hu0,
      IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hc0, add_zero] at hle
  have hposR : (0 : ℝ) < (tree.sumZ binoStepObj : ℝ) := by exact_mod_cast hpos
  linarith

/-- **Soundness of Subset-`J` Linear Bound Checker**:
A verified pure-integer `BinTree` certificate proves
`(expectedLb : ℝ) ≤ (objScale : ℝ) * (objSign : ℝ) * layerAvg f objK`. -/
theorem layerAvg_bound_of_bino_cert {n d : ℕ} (f : BooleanFun n)
    (hf : polyDegree f ≤ d)
    (hf0 : f (zeroVec n) = false)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true)
    (extraFix : List (ℕ × ℕ))
    (hextra : ∀ p ∈ extraFix, layerAvg (fun x => boolToReal (f x)) p.1 = (p.2 : ℝ))
    (tree : BinTree BinoStep) (objK : ℕ) (objSign : ℤ) (objScale : ℕ) (expectedLb : ℤ)
    (hcert : checkBinoBound n d extraFix tree objK objSign objScale expectedLb = true) :
    (expectedLb : ℝ) ≤
      (objScale : ℝ) * (objSign : ℝ) * layerAvg (fun x => boolToReal (f x)) objK := by
  unfold checkBinoBound at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcert
  obtain ⟨⟨⟨⟨⟨⟨hn, hd⟩, hobjK⟩, hok⟩, hu0⟩, hc0⟩, hlb⟩ := hcert
  obtain ⟨u, c, hu, hwfU, _, hle⟩ := binoTree_sound f hn hd hf hf0 hf1 extraFix hextra tree hok
  obtain ⟨_, hevFinal⟩ := wellFormed_and_eval_addEvalP u d objK (-(objScale : ℤ) * objSign)
    (IntTrie.mergeTree (binoStepU d) tree) hd hwfU
  rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hu0] at hevFinal
  rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hc0, add_zero] at hle
  rw [hu objK hobjK]
  have hlbR : (expectedLb : ℝ) ≤ (tree.sumZ binoStepObj : ℝ) := by exact_mod_cast hlb
  push_cast at hevFinal
  linarith

/-! #### `j`-Sliced Verifier for `BinomialBasisLP` (Low-Memory External Kernel Support) -/

/-- Depth-8 bivariate evaluation `scale * eval_h(j, a, b)` for a SINGLE fixed layer `j`. -/
def addEvalHJ (n d j a b : ℕ) (scale : ℤ) (t : IntTrie) : IntTrie :=
  if scale == 0 then t
  else addEvalHOuter n d j a b scale (min d (min j a) + 1) 0 1 t

/-- Single-layer (`j = jTarget`) depth-8 `cTrie` contribution of a `BinoStep`. -/
def binoStepCForJ (n d jTarget : ℕ) : BinoStep → IntTrie
  | .eqDiag j μ => if j == jTarget then addEvalHJ n d j j 0 μ .empty else .empty
  | .eqB00 j μ => if j == jTarget then addEvalHJ n d j 0 0 μ .empty else .empty
  | .eqB10 j μ => if j == jTarget then addEvalHJ n d j 1 0 μ .empty else .empty
  | .eqB01 j μ => if j == jTarget then addEvalHJ n d j 0 1 μ .empty else .empty
  | .eqSym i j t μ =>
      let t1 := if j == jTarget then addEvalHJ n d j t (i - t) μ .empty else .empty
      let t2 := if i == jTarget then addEvalHJ n d i t (j - t) (-μ) .empty else .empty
      IntTrie.merge t1 t2
  | .ubHGe0 j a b lam => if j == jTarget then addEvalHJ n d j a b (lam : ℤ) .empty else .empty
  | .ubHLePi j a b lam => if j == jTarget then addEvalHJ n d j a b (-(lam : ℤ)) .empty else .empty
  | .ubHLePj j a b lam => if j == jTarget then addEvalHJ n d j a b (-(lam : ℤ)) .empty else .empty
  | .ubHMcc j a b lam => if j == jTarget then addEvalHJ n d j a b (lam : ℤ) .empty else .empty
  | _ => .empty

/-- Check ONLY the depth-8 `c`-slice at layer `jTarget` (tiny per-layer arena in `con-ron`/`nanoda`). -/
def checkBinoCForJ (n d jTarget : ℕ) (tree : BinTree BinoStep) : Bool :=
  (IntTrie.mergeTree (binoStepCForJ n d jTarget) tree).isZero

/-- Check header + `uTrie` + positivity for a `j`-sliced Subset-`J` Farkas certificate. -/
def checkBinoFarkasU (n d : ℕ) (tree : BinTree BinoStep) : Bool :=
  decide (n < 64) && decide (d < 16) &&
    tree.all (binoStepOk n []) &&
    (IntTrie.mergeTree (binoStepU d) tree).isZero &&
    decide (0 < tree.sumZ binoStepObj)

/-- Check header + `uTrie` + bound for a `j`-sliced Subset-`J` LP bound certificate. -/
def checkBinoBoundU (n d : ℕ) (extraFix : List (ℕ × ℕ)) (tree : BinTree BinoStep)
    (objK : ℕ) (objSign : ℤ) (objScale : ℕ) (expectedLb : ℤ) : Bool :=
  decide (n < 64) && decide (d < 16) && decide (objK ≤ n) &&
    tree.all (binoStepOk n extraFix) &&
    (addEvalP d objK (-(objScale : ℤ) * objSign) (IntTrie.mergeTree (binoStepU d) tree)).isZero &&
    decide (expectedLb ≤ tree.sumZ binoStepObj)

lemma wellFormed_and_eval_addEvalHJ (cCoeff : ℕ → ℕ → ℕ → ℝ) (n d j a b : ℕ) (scale : ℤ)
    (t : IntTrie) (hd : d < 16) (ha : a ≤ j) (hb : b ≤ n - j)
    (hwf : IntTrie.WellFormed 8 t) :
    let cValJ : ℕ → ℝ := fun idx => cCoeff j (idx % 16) (idx / 16)
    IntTrie.WellFormed 8 (addEvalHJ n d j a b scale t) ∧
      IntTrie.evalTrie cValJ 1 0 (addEvalHJ n d j a b scale t) =
        IntTrie.evalTrie cValJ 1 0 t +
          (scale : ℝ) *
            ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
              cCoeff j r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) := by
  intro cValJ
  unfold addEvalHJ
  by_cases hs : scale = 0
  · subst hs; simp [hwf]
  · have hbeq : (scale == 0) = false := by simp [hs]
    rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
    set rMax := min d (min j a)
    obtain ⟨hwfO, hevO⟩ := wellFormed_and_eval_addEvalHOuter cValJ n d j a b 1 0
      scale hd hb (rMax + 1) 0 1 t (by omega) (by simp) hwf
    refine ⟨hwfO, ?_⟩
    rw [hevO]
    congr 2
    have hsub : Finset.range (rMax + 1) ⊆ Finset.range (d + 1) := Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl; intro r hr
      have hr16 : r < 16 := by simp only [Finset.mem_range] at hr; omega
      simp only [zero_add, one_mul]
      apply Finset.sum_congr rfl; intro sv hsv
      have hsv16 : sv < 16 := by simp only [Finset.mem_range] at hsv; omega
      have h1 : (r + 16 * sv) % 16 = r := by omega
      have h2 : (r + 16 * sv) / 16 = sv := by omega
      simp only [cValJ, h1, h2]
    · intro r hr hnot
      have hra : a < r := by simp only [Finset.mem_range] at hr hnot; omega
      apply Finset.sum_eq_zero; intro sv _
      simp [Nat.choose_eq_zero_of_lt hra]

private lemma binoStepCForJ_wf_and_sum (c : ℕ → ℕ → ℕ → ℝ) (n d : ℕ)
    (extraFix : List (ℕ × ℕ)) (hn : n < 64) (hd : d < 16)
    (step : BinoStep) (hok : binoStepOk n extraFix step = true) :
    let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
    let cValJ : ℕ → ℕ → ℝ := fun j idx => c j (idx % 16) (idx / 16)
    (∀ j ≤ n, IntTrie.WellFormed 8 (binoStepCForJ n d j step)) ∧
      IntTrie.evalTrie cVal 1 0 (binoStepC n d step) =
        ∑ j ∈ Finset.range (n + 1), IntTrie.evalTrie (cValJ j) 1 0 (binoStepCForJ n d j step) := by
  intro cVal cValJ
  have hsingle : ∀ (j₀ a b : ℕ) (sc : ℤ), j₀ ≤ n → a ≤ j₀ → b ≤ n - j₀ →
      (∀ j ≤ n, IntTrie.WellFormed 8 (if j₀ == j then addEvalHJ n d j₀ a b sc .empty else .empty)) ∧
      IntTrie.evalTrie cVal 1 0 (addEvalH n d j₀ a b sc .empty) =
        ∑ j ∈ Finset.range (n + 1),
          IntTrie.evalTrie (cValJ j) 1 0
            (if j₀ == j then addEvalHJ n d j₀ a b sc .empty else .empty) := by
    intro j₀ a b sc hj₀ ha hb
    obtain ⟨hwfH, hevH⟩ := wellFormed_and_eval_addEvalH c n d j₀ a b sc .empty hn hd hj₀ ha hb trivial
    obtain ⟨hwfJ, hevJ⟩ := wellFormed_and_eval_addEvalHJ c n d j₀ a b sc .empty hd ha hb trivial
    refine ⟨?_, ?_⟩
    · intro j _; split_ifs; exact hwfJ; exact trivial
    · rw [Finset.sum_eq_single j₀]
      · simp only [beq_self_eq_true, ↓reduceIte]
        rw [hevH, hevJ]; simp [IntTrie.evalTrie]
      · intro j _ hne
        have hbf : (j₀ == j) = false := by simp [hne.symm]
        simp [hbf, IntTrie.evalTrie]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
  cases step with
  | eqP0 _ | eqP1 _ | eqPFix _ _ _ | ubPLo _ _ | ubPHi _ _ =>
    exact ⟨fun _ _ => trivial, by simp [binoStepC, binoStepCForJ, IntTrie.evalTrie]⟩
  | eqDiag j μ =>
    simp only [binoStepOk, decide_eq_true_eq] at hok
    exact hsingle j j 0 μ hok (le_refl j) (Nat.zero_le _)
  | eqB00 j μ =>
    simp only [binoStepOk, decide_eq_true_eq] at hok
    exact hsingle j 0 0 μ hok (Nat.zero_le j) (Nat.zero_le _)
  | eqB10 j μ =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hsingle j 1 0 μ hok.2 hok.1 (Nat.zero_le _)
  | eqB01 j μ =>
    simp only [binoStepOk, decide_eq_true_eq] at hok
    exact hsingle j 0 1 μ (by omega) (Nat.zero_le j) (by omega)
  | ubHGe0 j a b lam =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hsingle j a b (lam : ℤ) hok.1.1 hok.1.2 hok.2
  | ubHLePi j a b lam =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hsingle j a b (-(lam : ℤ)) hok.1.1 hok.1.2 hok.2
  | ubHLePj j a b lam =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hsingle j a b (-(lam : ℤ)) hok.1.1 hok.1.2 hok.2
  | ubHMcc j a b lam =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hsingle j a b (lam : ℤ) hok.1.1 hok.1.2 hok.2
  | eqSym i j t μ =>
    simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hin, hjn⟩, hti⟩, htj⟩, hij⟩ := hok
    obtain ⟨hwf1, hev1⟩ := hsingle j t (i - t) μ hjn htj (by omega)
    obtain ⟨hwf2, hev2⟩ := hsingle i t (j - t) (-μ) hin hti (by omega)
    obtain ⟨hwfH1, hevH1⟩ := wellFormed_and_eval_addEvalH c n d j t (i - t) μ .empty hn hd hjn htj (by omega) trivial
    obtain ⟨_, hevH2⟩ := wellFormed_and_eval_addEvalH c n d i t (j - t) (-μ) _ hn hd hin hti (by omega) hwfH1
    obtain ⟨_, hevH2'⟩ := wellFormed_and_eval_addEvalH c n d i t (j - t) (-μ) .empty hn hd hin hti (by omega) trivial
    refine ⟨?_, ?_⟩
    · intro k hk
      exact (IntTrie.wellFormed_and_eval_merge (cValJ k) 8 1 0 _ _ (hwf1 k hk) (hwf2 k hk)).1
    · dsimp only [binoStepC, binoStepCForJ]
      have hmerge_sum :
          ∑ k ∈ Finset.range (n + 1),
            IntTrie.evalTrie (cValJ k) 1 0
              (IntTrie.merge (if j == k then addEvalHJ n d j t (i - t) μ .empty else .empty)
                             (if i == k then addEvalHJ n d i t (j - t) (-μ) .empty else .empty)) =
          (∑ k ∈ Finset.range (n + 1),
            IntTrie.evalTrie (cValJ k) 1 0
              (if j == k then addEvalHJ n d j t (i - t) μ .empty else .empty)) +
          (∑ k ∈ Finset.range (n + 1),
            IntTrie.evalTrie (cValJ k) 1 0
              (if i == k then addEvalHJ n d i t (j - t) (-μ) .empty else .empty)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k hk
        have hkn : k ≤ n := by rw [Finset.mem_range] at hk; omega
        exact (IntTrie.wellFormed_and_eval_merge (cValJ k) 8 1 0 _ _ (hwf1 k hkn) (hwf2 k hkn)).2
      rw [hmerge_sum, ← hev1, ← hev2, hevH2, hevH1, hevH2']
      simp [IntTrie.evalTrie]

private lemma binoTreeCForJ_wf_and_sum (c : ℕ → ℕ → ℕ → ℝ) (n d : ℕ)
    (extraFix : List (ℕ × ℕ)) (hn : n < 64) (hd : d < 16) :
    let cVal : ℕ → ℝ := fun idx => c (idx % 64) ((idx / 64) % 16) (idx / 1024)
    let cValJ : ℕ → ℕ → ℝ := fun j idx => c j (idx % 16) (idx / 16)
    ∀ (tree : BinTree BinoStep), tree.all (binoStepOk n extraFix) = true →
      (∀ j ≤ n, IntTrie.WellFormed 8 (IntTrie.mergeTree (binoStepCForJ n d j) tree)) ∧
      IntTrie.WellFormed 14 (IntTrie.mergeTree (binoStepC n d) tree) ∧
      IntTrie.evalTrie cVal 1 0 (IntTrie.mergeTree (binoStepC n d) tree) =
        ∑ j ∈ Finset.range (n + 1),
          IntTrie.evalTrie (cValJ j) 1 0 (IntTrie.mergeTree (binoStepCForJ n d j) tree) := by
  intro cVal cValJ tree
  induction tree with
  | empty =>
    intro _
    exact ⟨fun _ _ => trivial, trivial, by simp [IntTrie.mergeTree, IntTrie.evalTrie]⟩
  | leaf s =>
    intro hok
    dsimp only [BinTree.all] at hok
    obtain ⟨hwfJ, hsum⟩ := binoStepCForJ_wf_and_sum c n d extraFix hn hd s hok
    have hwfC : IntTrie.WellFormed 14 (binoStepC n d s) := by
      cases s with
      | eqP0 _ | eqP1 _ | eqPFix _ _ _ | ubPLo _ _ | ubPHi _ _ => exact trivial
      | eqDiag j μ =>
        simp only [binoStepOk, decide_eq_true_eq] at hok
        exact (wellFormed_and_eval_addEvalH c n d j j 0 μ .empty hn hd hok (le_refl j) (Nat.zero_le _) trivial).1
      | eqB00 j μ =>
        simp only [binoStepOk, decide_eq_true_eq] at hok
        exact (wellFormed_and_eval_addEvalH c n d j 0 0 μ .empty hn hd hok (Nat.zero_le j) (Nat.zero_le _) trivial).1
      | eqB10 j μ =>
        simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        exact (wellFormed_and_eval_addEvalH c n d j 1 0 μ .empty hn hd hok.2 hok.1 (Nat.zero_le _) trivial).1
      | eqB01 j μ =>
        simp only [binoStepOk, decide_eq_true_eq] at hok
        exact (wellFormed_and_eval_addEvalH c n d j 0 1 μ .empty hn hd (by omega) (Nat.zero_le j) (by omega) trivial).1
      | ubHGe0 j a b lam | ubHLePi j a b lam | ubHLePj j a b lam | ubHMcc j a b lam =>
        simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        exact (wellFormed_and_eval_addEvalH c n d j a b _ .empty hn hd hok.1.1 hok.1.2 hok.2 trivial).1
      | eqSym i j t μ =>
        simp only [binoStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨⟨⟨hin, hjn⟩, hti⟩, htj⟩, hij⟩ := hok
        have h1 := (wellFormed_and_eval_addEvalH c n d j t (i - t) μ .empty hn hd hjn htj (by omega) trivial).1
        exact (wellFormed_and_eval_addEvalH c n d i t (j - t) (-μ) _ hn hd hin hti (by omega) h1).1
    exact ⟨hwfJ, hwfC, hsum⟩
  | node l r ihl ihr =>
    intro hok
    simp only [BinTree.all, Bool.and_eq_true] at hok
    obtain ⟨hwfJl, hwfCl, hsuml⟩ := ihl hok.1
    obtain ⟨hwfJr, hwfCr, hsumr⟩ := ihr hok.2
    obtain ⟨hwfC, hevC⟩ := IntTrie.wellFormed_and_eval_merge cVal 14 1 0 _ _ hwfCl hwfCr
    refine ⟨?_, hwfC, ?_⟩
    · intro j hj
      exact (IntTrie.wellFormed_and_eval_merge (cValJ j) 8 1 0 _ _ (hwfJl j hj) (hwfJr j hj)).1
    · dsimp only [IntTrie.mergeTree]
      rw [hevC, hsuml, hsumr, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j hj
      have hjn : j ≤ n := by rw [Finset.mem_range] at hj; omega
      exact (IntTrie.wellFormed_and_eval_merge (cValJ j) 8 1 0 _ _ (hwfJl j hjn) (hwfJr j hjn)).2.symm

/-- **Soundness of `j`-Sliced Subset-`J` Farkas Checker**:
Each layer `j ≤ n` is verified independently via a tiny depth-8 `by decide` lemma. -/
theorem maxSensitivity_lt_of_bino_farkas_sliced {n d : ℕ} (tree : BinTree BinoStep)
    (hu : checkBinoFarkasU n d tree = true)
    (hc : ∀ j ≤ n, checkBinoCForJ n d j tree = true) :
    ∀ {m : ℕ} (f : BooleanFun m), polyDegree f ≤ d → maxSensitivity f < n := by
  unfold checkBinoFarkasU at hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
  obtain ⟨⟨⟨⟨hn, hd⟩, hok⟩, hu0⟩, hpos⟩ := hu
  apply maxSensitivity_lt_of_no_normalized
  rintro ⟨f, hdeg, hf0, hf1⟩
  obtain ⟨u, c, _, _, _, hle⟩ := binoTree_sound f hn hd hdeg hf0 hf1 [] (by simp) tree hok
  obtain ⟨_, _, hsumC⟩ := binoTreeCForJ_wf_and_sum c n d [] hn hd tree hok
  have hcZero : ∑ j ∈ Finset.range (n + 1),
      IntTrie.evalTrie (fun idx => c j (idx % 16) (idx / 16)) 1 0
        (IntTrie.mergeTree (binoStepCForJ n d j) tree) = 0 := by
    apply Finset.sum_eq_zero; intro j hj
    have hjn : j ≤ n := by rw [Finset.mem_range] at hj; omega
    exact IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ (hc j hjn)
  rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hu0, hsumC, hcZero, add_zero] at hle
  have hposR : (0 : ℝ) < (tree.sumZ binoStepObj : ℝ) := by exact_mod_cast hpos
  linarith

/-- **Soundness of `j`-Sliced Subset-`J` Linear Bound Checker**:
Each layer `j ≤ n` is verified independently via a tiny depth-8 `by decide` lemma. -/
theorem layerAvg_bound_of_bino_cert_sliced {n d : ℕ} (f : BooleanFun n)
    (hf : polyDegree f ≤ d)
    (hf0 : f (zeroVec n) = false)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true)
    (extraFix : List (ℕ × ℕ))
    (hextra : ∀ p ∈ extraFix, layerAvg (fun x => boolToReal (f x)) p.1 = (p.2 : ℝ))
    (tree : BinTree BinoStep) (objK : ℕ) (objSign : ℤ) (objScale : ℕ) (expectedLb : ℤ)
    (hu : checkBinoBoundU n d extraFix tree objK objSign objScale expectedLb = true)
    (hc : ∀ j ≤ n, checkBinoCForJ n d j tree = true) :
    (expectedLb : ℝ) ≤
      (objScale : ℝ) * (objSign : ℝ) * layerAvg (fun x => boolToReal (f x)) objK := by
  unfold checkBinoBoundU at hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
  obtain ⟨⟨⟨⟨⟨hn, hd⟩, hobjK⟩, hok⟩, hu0⟩, hlb⟩ := hu
  obtain ⟨u, c, hu', hwfU, _, hle⟩ := binoTree_sound f hn hd hf hf0 hf1 extraFix hextra tree hok
  obtain ⟨_, hevFinal⟩ := wellFormed_and_eval_addEvalP u d objK (-(objScale : ℤ) * objSign)
    (IntTrie.mergeTree (binoStepU d) tree) hd hwfU
  obtain ⟨_, _, hsumC⟩ := binoTreeCForJ_wf_and_sum c n d extraFix hn hd tree hok
  have hcZero : ∑ j ∈ Finset.range (n + 1),
      IntTrie.evalTrie (fun idx => c j (idx % 16) (idx / 16)) 1 0
        (IntTrie.mergeTree (binoStepCForJ n d j) tree) = 0 := by
    apply Finset.sum_eq_zero; intro j hj
    have hjn : j ≤ n := by rw [Finset.mem_range] at hj; omega
    exact IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ (hc j hjn)
  rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hu0] at hevFinal
  rw [hsumC, hcZero, add_zero] at hle
  rw [hu' objK hobjK]
  have hlbR : (expectedLb : ℝ) ≤ (tree.sumZ binoStepObj : ℝ) := by exact_mod_cast hlb
  push_cast at hevFinal
  linarith

/-! ### Part 4: Engine 2 — `TerwLPBound` (Direct Joint Terwilliger LP Bound Verifier) -/

/-- Canonical depth-15 key for `m(i, j, t)` with `i, j, t < 32`. -/
def canonMKey (i j t : ℕ) : ℕ :=
  if i ≤ j then i + 32 * (j + 32 * t) else j + 32 * (i + 32 * t)

/-- Constraint step in a pure-integer direct Joint Terwilliger LP certificate. -/
inductive TerwStep where
  | eqP0 (μ : ℤ)
  | eqP1 (μ : ℤ)
  | eqLayerSum (k s : ℕ) (μ : ℤ)
  | eqDiag (i : ℕ) (μ : ℤ)
  | eqB0 (j : ℕ) (μ : ℤ)
  | eqB11 (j : ℕ) (μ : ℤ)
  | eqB10 (j : ℕ) (μ : ℤ)
  | eqUnivar (k : ℕ) (μ : ℤ)
  | eqBivar (j r s a0 b0 : ℕ) (μ : ℤ)
  | eqHyp (i j si sj : ℕ) (μ : ℤ)
  | eqCustom (idx : ℕ) (μ : ℤ)
  | ubPLo (k : ℕ) (lam : ℕ)
  | ubPHi (k : ℕ) (lam : ℕ)
  | ubMLo (i j t : ℕ) (lam : ℕ)
  | ubMHi (i j t : ℕ) (lam : ℕ)
  | ubMLePi (i j t : ℕ) (lam : ℕ)
  | ubMLePj (i j t : ℕ) (lam : ℕ)
  | ubMMcc (i j t : ℕ) (lam : ℕ)
  deriving Repr, DecidableEq

/-- Add `scale * ∑_{u=0}^{d+1} (-1)^(d+1-u) C(d+1, u) p(k + u)` into depth-5 `pTrie`. -/
def addUnivarLoop (d1 k : ℕ) (scale : ℤ) : ℕ → ℕ → ℕ → IntTrie → IntTrie
  | 0, _, _, t => t
  | rem + 1, u, cur, t =>
      let coef := scale * (altSign (d1 - u) * (cur : ℤ))
      let t' := IntTrie.addAt 5 (k + u) coef t
      addUnivarLoop d1 k scale rem (u + 1) (cur * (d1 - u) / (u + 1)) t'

/-- Inner `v`-loop of `addBivarDiff` into depth-15 `mTrie`. -/
def addBivarInner (j s a0 b0 u : ℕ) (scaleU : ℤ) : ℕ → ℕ → ℕ → IntTrie → IntTrie
  | 0, _, _, t => t
  | rem + 1, v, curV, t =>
      let coef := scaleU * (altSign (s - v) * (curV : ℤ))
      let t' := IntTrie.addAt 15 (canonMKey (a0 + u + b0 + v) j (a0 + u)) coef t
      addBivarInner j s a0 b0 u scaleU rem (v + 1) (curV * (s - v) / (v + 1)) t'

/-- Outer `u`-loop of `addBivarDiff` into depth-15 `mTrie`. -/
def addBivarOuter (j r s a0 b0 : ℕ) (scale : ℤ) : ℕ → ℕ → ℕ → IntTrie → IntTrie
  | 0, _, _, t => t
  | rem + 1, u, curU, t =>
      let scaleU := scale * (altSign (r - u) * (curU : ℤ))
      let t' := addBivarInner j s a0 b0 u scaleU (s + 1) 0 1 t
      addBivarOuter j r s a0 b0 scale rem (u + 1) (curU * (r - u) / (u + 1)) t'

/-- Add `scale * C(n, i) * ∑_{t=tLo}^{tHi} C(i, t) C(n - i, j - t) m(i, j, t)` into `mTrie`. -/
def addHypLoop (n i j tLo : ℕ) (scaleCni : ℤ) : ℕ → ℕ → IntTrie → IntTrie
  | 0, _, t => t
  | rem + 1, off, t =>
      let tv := tLo + off
      let w : ℤ := ((fastChoose i tv * fastChoose (n - i) (j - tv) : ℕ) : ℤ)
      let t' := IntTrie.addAt 15 (canonMKey i j tv) (scaleCni * w) t
      addHypLoop n i j tLo scaleCni rem (off + 1) t'

/-- Add a sparse linear combination of `p(k)` terms into `pTrie`. -/
def addPList (scale : ℤ) : List (ℕ × ℤ) → IntTrie → IntTrie
  | [], t => t
  | (k, c) :: tl, t => addPList scale tl (IntTrie.addAt 5 k (scale * c) t)

/-- Add a sparse linear combination of `m(i, j, t)` terms into `mTrie`. -/
def addMList (scale : ℤ) : List (ℕ × ℕ × ℕ × ℤ) → IntTrie → IntTrie
  | [], t => t
  | (i, j, tv, c) :: tl, t => addMList scale tl (IntTrie.addAt 15 (canonMKey i j tv) (scale * c) t)

/-- Check validity of a triple `(i, j, t)` in dimension `n`. -/
def validTripleB (n i j t : ℕ) : Bool :=
  decide (i ≤ n) && decide (j ≤ n) && decide (t ≤ i) && decide (t ≤ j) && decide (i + j ≤ n + t)

/-- Side-condition check for a single `TerwStep`. -/
def terwStepOk (n d : ℕ) (layerSums : List (ℕ × ℕ))
    (customEqs : List (List (ℕ × ℕ × ℕ × ℤ) × ℤ)) : TerwStep → Bool
  | .eqP0 _ => true
  | .eqP1 _ => decide (1 ≤ n)
  | .eqLayerSum k s _ => decide (k ≤ n) && layerSums.contains (k, s)
  | .eqDiag i _ => decide (i ≤ n)
  | .eqB0 j _ => decide (j ≤ n)
  | .eqB11 j _ => decide (1 ≤ j) && decide (j ≤ n)
  | .eqB10 j _ => decide (j + 1 ≤ n)
  | .eqUnivar k _ => decide (k + d + 1 ≤ n)
  | .eqBivar j r s a0 b0 _ =>
      decide (j ≤ n) && (r + s == d + 1) && decide (a0 + r ≤ j) && decide (b0 + s ≤ n - j)
  | .eqHyp i j si sj _ =>
      decide (i ≤ n) && decide (j ≤ n) && layerSums.contains (i, si) && layerSums.contains (j, sj)
  | .eqCustom idx _ => (customEqs[idx]?).isSome
  | .ubPLo k _ => decide (k ≤ n)
  | .ubPHi k _ => decide (k ≤ n)
  | .ubMLo i j t _ => validTripleB n i j t
  | .ubMHi i j t _ => validTripleB n i j t
  | .ubMLePi i j t _ => validTripleB n i j t
  | .ubMLePj i j t _ => validTripleB n i j t
  | .ubMMcc i j t _ => validTripleB n i j t

/-- `pTrie` contribution of a single `TerwStep`. -/
def terwStepP (n d : ℕ) : TerwStep → IntTrie
  | .eqP0 μ => IntTrie.addAt 5 0 μ .empty
  | .eqP1 μ => IntTrie.addAt 5 1 μ .empty
  | .eqLayerSum k _ μ => IntTrie.addAt 5 k (μ * (fastChoose n k : ℤ)) .empty
  | .eqDiag i μ => IntTrie.addAt 5 i (-μ) .empty
  | .eqB0 _ _ => .empty
  | .eqB11 j μ => IntTrie.addAt 5 j (-μ) .empty
  | .eqB10 j μ => IntTrie.addAt 5 j (-μ) .empty
  | .eqUnivar k μ => addUnivarLoop (d + 1) k μ (d + 2) 0 1 .empty
  | .eqBivar _ _ _ _ _ _ => .empty
  | .eqHyp _ _ _ _ _ => .empty
  | .eqCustom _ _ => .empty
  | .ubPLo k lam => IntTrie.addAt 5 k (lam : ℤ) .empty
  | .ubPHi k lam => IntTrie.addAt 5 k (-(lam : ℤ)) .empty
  | .ubMLo _ _ _ _ => .empty
  | .ubMHi _ _ _ _ => .empty
  | .ubMLePi i _ _ lam => IntTrie.addAt 5 i (lam : ℤ) .empty
  | .ubMLePj _ j _ lam => IntTrie.addAt 5 j (lam : ℤ) .empty
  | .ubMMcc i j _ lam => IntTrie.addAt 5 j (-(lam : ℤ)) (IntTrie.addAt 5 i (-(lam : ℤ)) .empty)

/-- `mTrie` contribution of a single `TerwStep`. -/
def terwStepM (n : ℕ) (customEqs : List (List (ℕ × ℕ × ℕ × ℤ) × ℤ)) : TerwStep → IntTrie
  | .eqP0 _ => .empty
  | .eqP1 _ => .empty
  | .eqLayerSum _ _ _ => .empty
  | .eqDiag i μ => IntTrie.addAt 15 (canonMKey i i i) μ .empty
  | .eqB0 j μ => IntTrie.addAt 15 (canonMKey 0 j 0) μ .empty
  | .eqB11 j μ => IntTrie.addAt 15 (canonMKey 1 j 1) μ .empty
  | .eqB10 j μ => IntTrie.addAt 15 (canonMKey 1 j 0) μ .empty
  | .eqUnivar _ _ => .empty
  | .eqBivar j r s a0 b0 μ => addBivarOuter j r s a0 b0 μ (r + 1) 0 1 .empty
  | .eqHyp i j _ _ μ =>
      let tLo := i + j - n
      let tHi := min i j
      addHypLoop n i j tLo (μ * (fastChoose n i : ℤ)) (tHi - tLo + 1) 0 .empty
  | .eqCustom idx μ =>
      match customEqs[idx]? with
      | some (terms, _) => addMList μ terms .empty
      | none => .empty
  | .ubPLo _ _ => .empty
  | .ubPHi _ _ => .empty
  | .ubMLo i j t lam => IntTrie.addAt 15 (canonMKey i j t) (lam : ℤ) .empty
  | .ubMHi i j t lam => IntTrie.addAt 15 (canonMKey i j t) (-(lam : ℤ)) .empty
  | .ubMLePi i j t lam => IntTrie.addAt 15 (canonMKey i j t) (-(lam : ℤ)) .empty
  | .ubMLePj i j t lam => IntTrie.addAt 15 (canonMKey i j t) (-(lam : ℤ)) .empty
  | .ubMMcc i j t lam => IntTrie.addAt 15 (canonMKey i j t) (lam : ℤ) .empty

/-- Dual-objective contribution of a single `TerwStep`. -/
def terwStepObj (customEqs : List (List (ℕ × ℕ × ℕ × ℤ) × ℤ)) : TerwStep → ℤ
  | .eqP0 _ => 0
  | .eqP1 μ => μ
  | .eqLayerSum _ s μ => μ * (s : ℤ)
  | .eqDiag _ _ => 0
  | .eqB0 _ _ => 0
  | .eqB11 _ _ => 0
  | .eqB10 _ _ => 0
  | .eqUnivar _ _ => 0
  | .eqBivar _ _ _ _ _ _ => 0
  | .eqHyp _ _ si sj μ => μ * ((si * sj : ℕ) : ℤ)
  | .eqCustom idx μ =>
      match customEqs[idx]? with
      | some (_, rhs) => μ * rhs
      | none => 0
  | .ubPLo _ _ => 0
  | .ubPHi _ lam => -(lam : ℤ)
  | .ubMLo _ _ _ _ => 0
  | .ubMHi _ _ _ lam => -(lam : ℤ)
  | .ubMLePi _ _ _ _ => 0
  | .ubMLePj _ _ _ _ => 0
  | .ubMMcc _ _ _ lam => -(lam : ℤ)

/-- Pure-integer checker for a linear lower bound in the direct Joint Terwilliger LP. -/
def checkTerwLPBound (n d : ℕ) (layerSums : List (ℕ × ℕ))
    (customEqs : List (List (ℕ × ℕ × ℕ × ℤ) × ℤ)) (tree : BinTree TerwStep)
    (targetP : List (ℕ × ℤ)) (targetM : List (ℕ × ℕ × ℕ × ℤ))
    (scale : ℕ) (expectedLb : ℤ) : Bool :=
  decide (n < 32) &&
    targetP.all (fun p => decide (p.1 ≤ n)) &&
    targetM.all (fun q => validTripleB n q.1 q.2.1 q.2.2.1) &&
    tree.all (terwStepOk n d layerSums customEqs) &&
    (addPList (-(scale : ℤ)) targetP (IntTrie.mergeTree (terwStepP n d) tree)).isZero &&
    (addMList (-(scale : ℤ)) targetM (IntTrie.mergeTree (terwStepM n customEqs) tree)).isZero &&
    decide (expectedLb ≤ tree.sumZ (terwStepObj customEqs))

/-- Semantic evaluation of a sparse `p(k)` objective list. -/
noncomputable def evalTargetP {n : ℕ} (f : BooleanFun n) : List (ℕ × ℤ) → ℝ
  | [] => 0
  | (k, c) :: tl => (c : ℝ) * layerAvg (fun x => boolToReal (f x)) k + evalTargetP f tl

/-- Semantic evaluation of a sparse `m(i, j, t)` objective list. -/
noncomputable def evalTargetM {n : ℕ} (f : BooleanFun n) : List (ℕ × ℕ × ℕ × ℤ) → ℝ
  | [] => 0
  | (i, j, t, c) :: tl => (c : ℝ) * pairCorr f i j t + evalTargetM f tl

/-! #### Soundness of `TerwLPBound` -/

lemma validTripleB_iff (n i j t : ℕ) :
    validTripleB n i j t = true ↔ ValidTriple n i j t := by
  unfold validTripleB ValidTriple
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  tauto

lemma canonMKey_lt (i j t : ℕ) (hi : i < 32) (hj : j < 32) (ht : t < 32) :
    canonMKey i j t < 2 ^ 15 := by
  unfold canonMKey
  split_ifs <;> omega

noncomputable def terwMVal {n : ℕ} (f : BooleanFun n) (idx : ℕ) : ℝ :=
  pairCorr f (idx % 32) ((idx / 32) % 32) (idx / 1024)

lemma terwMVal_canonMKey {n i j t : ℕ} (f : BooleanFun n) (hn : n < 32)
    (hvalid : ValidTriple n i j t) :
    terwMVal f (canonMKey i j t) = pairCorr f i j t := by
  have ⟨hin, hjn, hti, htj, _⟩ := hvalid
  have hi32 : i < 32 := by omega
  have hj32 : j < 32 := by omega
  have ht32 : t < 32 := by omega
  unfold canonMKey terwMVal
  split_ifs with hij
  · have h1 : (i + 32 * (j + 32 * t)) % 32 = i := by omega
    have h2 : ((i + 32 * (j + 32 * t)) / 32) % 32 = j := by omega
    have h3 : (i + 32 * (j + 32 * t)) / 1024 = t := by omega
    rw [h1, h2, h3]
  · have h1 : (j + 32 * (i + 32 * t)) % 32 = j := by omega
    have h2 : ((j + 32 * (i + 32 * t)) / 32) % 32 = i := by omega
    have h3 : (j + 32 * (i + 32 * t)) / 1024 = t := by omega
    rw [h1, h2, h3]
    exact (pairCorr_symm f hvalid).symm

private lemma wellFormed_and_eval_addUnivarLoop (pVal : ℕ → ℝ) (d1 k : ℕ) (scale : ℤ) :
    ∀ rem u cur t,
      k + u + rem ≤ 32 → cur = Nat.choose d1 u → IntTrie.WellFormed 5 t →
      IntTrie.WellFormed 5 (addUnivarLoop d1 k scale rem u cur t) ∧
        IntTrie.evalTrie pVal 1 0 (addUnivarLoop d1 k scale rem u cur t) =
          IntTrie.evalTrie pVal 1 0 t +
            (scale : ℝ) *
              ∑ m ∈ Finset.range rem,
                (((-1 : ℤ) ^ (d1 - (u + m)) * (Nat.choose d1 (u + m) : ℤ) : ℤ) : ℝ) *
                  pVal (k + (u + m))
  | 0, _, _, t, _, _, hwf => by simp [addUnivarLoop, hwf]
  | rem + 1, u, cur, t, hlt, hcur, hwf => by
    simp only [addUnivarLoop]
    have hku : k + u < 2 ^ 5 := by omega
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 (k + u) 1 0
      (scale * (altSign (d1 - u) * (cur : ℤ))) t hku hwf
    have hnext : cur * (d1 - u) / (u + 1) = Nat.choose d1 (u + 1) := by
      rw [hcur]; exact choose_step_div d1 u
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addUnivarLoop pVal d1 k scale rem (u + 1)
      (cur * (d1 - u) / (u + 1)) _ (by omega) hnext hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1, Finset.sum_range_succ', hcur, altSign_eq]
    have hshift :
        ∑ m ∈ Finset.range rem,
          (((-1 : ℤ) ^ (d1 - (u + 1 + m)) * (Nat.choose d1 (u + 1 + m) : ℤ) : ℤ) : ℝ) *
            pVal (k + (u + 1 + m)) =
        ∑ m ∈ Finset.range rem,
          (((-1 : ℤ) ^ (d1 - (u + (m + 1))) * (Nat.choose d1 (u + (m + 1)) : ℤ) : ℤ) : ℝ) *
            pVal (k + (u + (m + 1))) := by
      apply Finset.sum_congr rfl; intro m _
      have : u + 1 + m = u + (m + 1) := by omega
      rw [this]
    rw [hshift]
    simp only [zero_add, one_mul, Nat.add_zero]
    push_cast; ring

private lemma wellFormed_and_eval_addBivarInner {n : ℕ} (f : BooleanFun n)
    (hn : n < 32) (j s a0 b0 u : ℕ) (scaleU : ℤ)
    (hj : j ≤ n) (hau : a0 + u ≤ j) :
    ∀ rem v curV t,
      b0 + v + rem ≤ n - j + 1 → curV = Nat.choose s v → IntTrie.WellFormed 15 t →
      IntTrie.WellFormed 15 (addBivarInner j s a0 b0 u scaleU rem v curV t) ∧
        IntTrie.evalTrie (terwMVal f) 1 0 (addBivarInner j s a0 b0 u scaleU rem v curV t) =
          IntTrie.evalTrie (terwMVal f) 1 0 t +
            (scaleU : ℝ) *
              ∑ m ∈ Finset.range rem,
                (((-1 : ℤ) ^ (s - (v + m)) * (Nat.choose s (v + m) : ℤ) : ℤ) : ℝ) *
                  pairCorr f (a0 + u + b0 + (v + m)) j (a0 + u)
  | 0, _, _, t, _, _, hwf => by simp [addBivarInner, hwf]
  | rem + 1, v, curV, t, hlt, hcur, hwf => by
    simp only [addBivarInner]
    have hvalid : ValidTriple n (a0 + u + b0 + v) j (a0 + u) :=
      ⟨by omega, hj, by omega, hau, by omega⟩
    have hkey : canonMKey (a0 + u + b0 + v) j (a0 + u) < 2 ^ 15 :=
      canonMKey_lt _ _ _ (by omega) (by omega) (by omega)
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15
      (canonMKey (a0 + u + b0 + v) j (a0 + u)) 1 0
      (scaleU * (altSign (s - v) * (curV : ℤ))) t hkey hwf
    have hnext : curV * (s - v) / (v + 1) = Nat.choose s (v + 1) := by
      rw [hcur]; exact choose_step_div s v
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addBivarInner f hn j s a0 b0 u scaleU hj hau rem (v + 1)
      (curV * (s - v) / (v + 1)) _ (by omega) hnext hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1, Finset.sum_range_succ', hcur, altSign_eq]
    have hshift :
        ∑ m ∈ Finset.range rem,
          (((-1 : ℤ) ^ (s - (v + 1 + m)) * (Nat.choose s (v + 1 + m) : ℤ) : ℤ) : ℝ) *
            pairCorr f (a0 + u + b0 + (v + 1 + m)) j (a0 + u) =
        ∑ m ∈ Finset.range rem,
          (((-1 : ℤ) ^ (s - (v + (m + 1))) * (Nat.choose s (v + (m + 1)) : ℤ) : ℤ) : ℝ) *
            pairCorr f (a0 + u + b0 + (v + (m + 1))) j (a0 + u) := by
      apply Finset.sum_congr rfl; intro m _
      have : v + 1 + m = v + (m + 1) := by omega
      rw [this]
    rw [hshift]
    simp only [zero_add, one_mul, Nat.add_zero]
    rw [terwMVal_canonMKey f hn hvalid]
    push_cast; ring

private lemma wellFormed_and_eval_addBivarOuter {n : ℕ} (f : BooleanFun n)
    (hn : n < 32) (j r s a0 b0 : ℕ) (scale : ℤ)
    (hj : j ≤ n) (hb0 : b0 + s ≤ n - j) :
    ∀ rem u curU t,
      a0 + u + rem ≤ j + 1 → curU = Nat.choose r u → IntTrie.WellFormed 15 t →
      IntTrie.WellFormed 15 (addBivarOuter j r s a0 b0 scale rem u curU t) ∧
        IntTrie.evalTrie (terwMVal f) 1 0 (addBivarOuter j r s a0 b0 scale rem u curU t) =
          IntTrie.evalTrie (terwMVal f) 1 0 t +
            (scale : ℝ) *
              ∑ m ∈ Finset.range rem, ∑ v ∈ Finset.range (s + 1),
                ((((-1 : ℤ) ^ (r - (u + m)) * (Nat.choose r (u + m) : ℤ)) *
                  ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
                  pairCorr f (a0 + (u + m) + b0 + v) j (a0 + (u + m))
  | 0, _, _, t, _, _, hwf => by simp [addBivarOuter, hwf]
  | rem + 1, u, curU, t, hlt, hcur, hwf => by
    simp only [addBivarOuter]
    obtain ⟨hwf1, hev1⟩ := wellFormed_and_eval_addBivarInner f hn j s a0 b0 u
      (scale * (altSign (r - u) * (curU : ℤ))) hj (by omega) (s + 1) 0 1 t (by omega) (by simp) hwf
    have hnext : curU * (r - u) / (u + 1) = Nat.choose r (u + 1) := by
      rw [hcur]; exact choose_step_div r u
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addBivarOuter f hn j r s a0 b0 scale hj hb0
      rem (u + 1) (curU * (r - u) / (u + 1)) _ (by omega) hnext hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1, hcur, altSign_eq]
    have houter_succ :
        ∑ m ∈ Finset.range (rem + 1), ∑ v ∈ Finset.range (s + 1),
          ((((-1 : ℤ) ^ (r - (u + m)) * (Nat.choose r (u + m) : ℤ)) *
            ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
            pairCorr f (a0 + (u + m) + b0 + v) j (a0 + (u + m)) =
        (∑ m ∈ Finset.range rem, ∑ v ∈ Finset.range (s + 1),
          ((((-1 : ℤ) ^ (r - (u + (m + 1))) * (Nat.choose r (u + (m + 1)) : ℤ)) *
            ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
            pairCorr f (a0 + (u + (m + 1)) + b0 + v) j (a0 + (u + (m + 1)))) +
        ∑ v ∈ Finset.range (s + 1),
          ((((-1 : ℤ) ^ (r - (u + 0)) * (Nat.choose r (u + 0) : ℤ)) *
            ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
            pairCorr f (a0 + (u + 0) + b0 + v) j (a0 + (u + 0)) :=
      Finset.sum_range_succ' _ rem
    rw [houter_succ]
    have hshift :
        ∑ m ∈ Finset.range rem, ∑ v ∈ Finset.range (s + 1),
          ((((-1 : ℤ) ^ (r - (u + 1 + m)) * (Nat.choose r (u + 1 + m) : ℤ)) *
            ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
            pairCorr f (a0 + (u + 1 + m) + b0 + v) j (a0 + (u + 1 + m)) =
        ∑ m ∈ Finset.range rem, ∑ v ∈ Finset.range (s + 1),
          ((((-1 : ℤ) ^ (r - (u + (m + 1))) * (Nat.choose r (u + (m + 1)) : ℤ)) *
            ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
            pairCorr f (a0 + (u + (m + 1)) + b0 + v) j (a0 + (u + (m + 1))) := by
      apply Finset.sum_congr rfl; intro m _
      have : u + 1 + m = u + (m + 1) := by omega
      rw [this]
    rw [hshift]
    have hrow0 :
        ((scale * ((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ)) : ℤ) : ℝ) *
          ∑ m ∈ Finset.range (s + 1),
            (((-1 : ℤ) ^ (s - (0 + m)) * (Nat.choose s (0 + m) : ℤ) : ℤ) : ℝ) *
              pairCorr f (a0 + u + b0 + (0 + m)) j (a0 + u) =
        (scale : ℝ) *
          ∑ v ∈ Finset.range (s + 1),
            ((((-1 : ℤ) ^ (r - (u + 0)) * (Nat.choose r (u + 0) : ℤ)) *
              ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
              pairCorr f (a0 + (u + 0) + b0 + v) j (a0 + (u + 0)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _
      simp only [zero_add, Nat.add_zero]
      push_cast; ring
    rw [hrow0]
    ring

lemma wellFormed_and_eval_addHypLoop {n : ℕ} (f : BooleanFun n)
    (hn : n < 32) (i j tLo : ℕ) (scaleCni : ℤ)
    (hi : i ≤ n) (hj : j ≤ n) (htLo : i + j - n ≤ tLo) :
    ∀ rem off t,
      tLo + off + rem ≤ min i j + 1 → IntTrie.WellFormed 15 t →
      IntTrie.WellFormed 15 (addHypLoop n i j tLo scaleCni rem off t) ∧
        IntTrie.evalTrie (terwMVal f) 1 0 (addHypLoop n i j tLo scaleCni rem off t) =
          IntTrie.evalTrie (terwMVal f) 1 0 t +
            (scaleCni : ℝ) *
              ∑ m ∈ Finset.range rem,
                (Nat.choose i (tLo + (off + m)) *
                  Nat.choose (n - i) (j - (tLo + (off + m))) : ℝ) *
                  pairCorr f i j (tLo + (off + m))
  | 0, _, t, _, hwf => by simp [addHypLoop, hwf]
  | rem + 1, off, t, hlt, hwf => by
    simp only [addHypLoop]
    have hvalid : ValidTriple n i j (tLo + off) := ⟨hi, hj, by omega, by omega, by omega⟩
    have hkey : canonMKey i j (tLo + off) < 2 ^ 15 :=
      canonMKey_lt _ _ _ (by omega) (by omega) (by omega)
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15
      (canonMKey i j (tLo + off)) 1 0
      (scaleCni * ((fastChoose i (tLo + off) * fastChoose (n - i) (j - (tLo + off)) : ℕ) : ℤ))
      t hkey hwf
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addHypLoop f hn i j tLo scaleCni hi hj htLo
      rem (off + 1) _ (by omega) hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1, Finset.sum_range_succ', fastChoose_eq, fastChoose_eq]
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
    simp only [zero_add, one_mul, Nat.add_zero]
    rw [terwMVal_canonMKey f hn hvalid]
    push_cast; ring

private lemma wellFormed_and_eval_addPList {n : ℕ} (f : BooleanFun n) (hn : n < 32) (scale : ℤ) :
    ∀ l t,
      (∀ p ∈ l, p.1 ≤ n) → IntTrie.WellFormed 5 t →
      IntTrie.WellFormed 5 (addPList scale l t) ∧
        IntTrie.evalTrie (fun k => layerAvg (fun x => boolToReal (f x)) k) 1 0 (addPList scale l t) =
          IntTrie.evalTrie (fun k => layerAvg (fun x => boolToReal (f x)) k) 1 0 t +
            (scale : ℝ) * evalTargetP f l
  | [], t, _, hwf => by simp [addPList, evalTargetP, hwf]
  | (k, c) :: tl, t, hall, hwf => by
    simp only [addPList, evalTargetP]
    have hk : k ≤ n := hall (k, c) (List.mem_cons_self ..)
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_addAt
      (fun j => layerAvg (fun x => boolToReal (f x)) j) 5 k 1 0 (scale * c) t (by omega) hwf
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addPList f hn scale tl _
      (fun p hp => hall p (List.mem_cons_of_mem _ hp)) hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1]; simp only [zero_add, one_mul]; push_cast; ring

lemma wellFormed_and_eval_addMList {n : ℕ} (f : BooleanFun n) (hn : n < 32) (scale : ℤ) :
    ∀ l t,
      (∀ q ∈ l, ValidTriple n q.1 q.2.1 q.2.2.1) → IntTrie.WellFormed 15 t →
      IntTrie.WellFormed 15 (addMList scale l t) ∧
        IntTrie.evalTrie (terwMVal f) 1 0 (addMList scale l t) =
          IntTrie.evalTrie (terwMVal f) 1 0 t +
            (scale : ℝ) * evalTargetM f l
  | [], t, _, hwf => by simp [addMList, evalTargetM, hwf]
  | (i, j, tv, c) :: tl, t, hall, hwf => by
    simp only [addMList, evalTargetM]
    have hvalid : ValidTriple n i j tv := hall (i, j, tv, c) (List.mem_cons_self ..)
    have hkey : canonMKey i j tv < 2 ^ 15 :=
      canonMKey_lt _ _ _ (by have := hvalid.1; omega) (by have := hvalid.2.1; omega)
        (by have := hvalid.1; have := hvalid.2.2.1; omega)
    obtain ⟨hwf1, hev1⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15
      (canonMKey i j tv) 1 0 (scale * c) t hkey hwf
    obtain ⟨hwf2, hev2⟩ := wellFormed_and_eval_addMList f hn scale tl _
      (fun q hq => hall q (List.mem_cons_of_mem _ hq)) hwf1
    refine ⟨hwf2, ?_⟩
    rw [hev2, hev1]; simp only [zero_add, one_mul]
    rw [terwMVal_canonMKey f hn hvalid]
    push_cast; ring

/-- Single-step soundness for `TerwLPBound`. -/
private lemma terwStep_sound {n d : ℕ} (f : BooleanFun n)
    (hn : n < 32)
    (hf : polyDegree f ≤ d)
    (hf0 : f (zeroVec n) = false)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true)
    (layerSums : List (ℕ × ℕ))
    (hlayers : ∀ p ∈ layerSums, realLayerSum (fun x => boolToReal (f x)) p.1 = (p.2 : ℝ))
    (customEqs : List (List (ℕ × ℕ × ℕ × ℤ) × ℤ))
    (hcustom : ∀ eq ∈ customEqs,
      (∀ q ∈ eq.1, ValidTriple n q.1 q.2.1 q.2.2.1) ∧ evalTargetM f eq.1 = (eq.2 : ℝ))
    (step : TerwStep) (hok : terwStepOk n d layerSums customEqs step = true) :
    let pVal : ℕ → ℝ := fun k => layerAvg (fun x => boolToReal (f x)) k
    IntTrie.WellFormed 5 (terwStepP n d step) ∧
      IntTrie.WellFormed 15 (terwStepM n customEqs step) ∧
      (terwStepObj customEqs step : ℝ) ≤
        IntTrie.evalTrie pVal 1 0 (terwStepP n d step) +
        IntTrie.evalTrie (terwMVal f) 1 0 (terwStepM n customEqs step) := by
  intro pVal
  cases step with
  | eqP0 μ =>
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 0 1 0 μ .empty (by omega) trivial
    refine ⟨hwfP, trivial, ?_⟩
    dsimp only [terwStepObj, terwStepP, terwStepM]
    rw [hevP]; simp [IntTrie.evalTrie, pVal, layerAvg_bool_zero hf0]
  | eqP1 μ =>
    simp only [terwStepOk, decide_eq_true_eq] at hok
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 1 1 0 μ .empty (by omega) trivial
    refine ⟨hwfP, trivial, ?_⟩
    dsimp only [terwStepObj, terwStepP, terwStepM]
    rw [hevP]; simp only [IntTrie.evalTrie, zero_add, mul_one, pVal, layerAvg_bool_one (by omega) hf1]
    linarith
  | eqLayerSum k s μ =>
    simp only [terwStepOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem] at hok
    obtain ⟨hkn, hmem⟩ := hok
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 k 1 0
      (μ * (fastChoose n k : ℤ)) .empty (by omega) trivial
    have hcpos : (Nat.choose n k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
    have hmul : (Nat.choose n k : ℝ) * pVal k = (s : ℝ) := by
      simp only [pVal, layerAvg]; rw [mul_div_cancel₀ _ hcpos]; exact hlayers (k, s) hmem
    refine ⟨hwfP, trivial, ?_⟩
    dsimp only [terwStepObj, terwStepP, terwStepM]
    rw [hevP]; simp only [IntTrie.evalTrie, zero_add, one_mul, fastChoose_eq]
    have : ((μ * (Nat.choose n k : ℤ) : ℤ) : ℝ) * pVal k = (μ : ℝ) * (s : ℝ) := by
      push_cast; rw [mul_assoc, hmul]
    rw [this]; push_cast; linarith
  | eqDiag i μ =>
    simp only [terwStepOk, decide_eq_true_eq] at hok
    have hvalid : ValidTriple n i i i := ⟨hok, hok, le_refl i, le_refl i, by omega⟩
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 i 1 0 (-μ) .empty (by omega) trivial
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i i i) 1 0
      μ .empty (canonMKey_lt _ _ _ (by omega) (by omega) (by omega)) trivial
    refine ⟨hwfP, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevP, hevM, IntTrie.evalTrie, zero_add, one_mul,
      terwMVal_canonMKey f hn hvalid, pairCorr_diag f hok]
    push_cast; linarith
  | eqB0 j μ =>
    simp only [terwStepOk, decide_eq_true_eq] at hok
    have hvalid : ValidTriple n 0 j 0 := ⟨Nat.zero_le n, hok, le_refl 0, Nat.zero_le j, by omega⟩
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey 0 j 0) 1 0
      μ .empty (canonMKey_lt _ _ _ (by omega) (by omega) (by omega)) trivial
    refine ⟨trivial, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevM, IntTrie.evalTrie, zero_add, one_mul,
      terwMVal_canonMKey f hn hvalid, pairCorr_zero_left f hf0]; norm_num
  | eqB11 j μ =>
    simp only [terwStepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj1, hjn⟩ := hok
    have hvalid : ValidTriple n 1 j 1 := ⟨by omega, hjn, le_refl 1, hj1, by omega⟩
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 j 1 0 (-μ) .empty (by omega) trivial
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey 1 j 1) 1 0
      μ .empty (canonMKey_lt _ _ _ (by omega) (by omega) (by omega)) trivial
    refine ⟨hwfP, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevP, hevM, IntTrie.evalTrie, zero_add, one_mul,
      terwMVal_canonMKey f hn hvalid, pairCorr_one_left_one f hj1 hjn hf1]
    push_cast; linarith
  | eqB10 j μ =>
    simp only [terwStepOk, decide_eq_true_eq] at hok
    have hvalid : ValidTriple n 1 j 0 := ⟨by omega, by omega, by omega, by omega, by omega⟩
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 j 1 0 (-μ) .empty (by omega) trivial
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey 1 j 0) 1 0
      μ .empty (canonMKey_lt _ _ _ (by omega) (by omega) (by omega)) trivial
    refine ⟨hwfP, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevP, hevM, IntTrie.evalTrie, zero_add, one_mul,
      terwMVal_canonMKey f hn hvalid, pairCorr_one_left_zero f hok hf1]
    push_cast; linarith
  | eqUnivar k μ =>
    simp only [terwStepOk, decide_eq_true_eq] at hok
    obtain ⟨hwfP, hevP⟩ := wellFormed_and_eval_addUnivarLoop pVal (d + 1) k μ (d + 2) 0 1 .empty
      (by omega) (by simp) trivial
    have h0 : ∑ m ∈ Finset.range (d + 2),
        (((-1 : ℤ) ^ (d + 1 - (0 + m)) * (Nat.choose (d + 1) (0 + m) : ℤ) : ℤ) : ℝ) *
          pVal (k + (0 + m)) = 0 := by
      simp only [zero_add, pVal]
      have hdiff := layerAvg_finDiff_eq_zero f hf hok
      convert hdiff using 2 with u; push_cast; ring
    refine ⟨hwfP, trivial, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevP, h0, IntTrie.evalTrie]; norm_num
  | eqBivar j r s a0 b0 μ =>
    simp only [terwStepOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨hjn, hrs⟩, ha0⟩, hb0⟩ := hok
    obtain ⟨hwfM, hevM⟩ := wellFormed_and_eval_addBivarOuter f hn j r s a0 b0 μ hjn hb0
      (r + 1) 0 1 .empty (by omega) (by simp) trivial
    have h0 : ∑ m ∈ Finset.range (r + 1), ∑ v ∈ Finset.range (s + 1),
        ((((-1 : ℤ) ^ (r - (0 + m)) * (Nat.choose r (0 + m) : ℤ)) *
          ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
          pairCorr f (a0 + (0 + m) + b0 + v) j (a0 + (0 + m)) = 0 := by
      simp only [zero_add]; exact pairCorr_bivarDiff_eq_zero f hf hjn hrs ha0 hb0
    refine ⟨trivial, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevM, h0, IntTrie.evalTrie]; norm_num
  | eqHyp i j si sj μ =>
    simp only [terwStepOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem] at hok
    obtain ⟨⟨⟨hin, hjn⟩, hmemi⟩, hmemj⟩ := hok
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
      · intro tv htv
        rw [Finset.mem_coe, Finset.mem_Icc] at htv
        refine ⟨tv - tLo, ?_, by dsimp only; omega⟩
        rw [Finset.mem_coe, Finset.mem_range]; omega
      · intro m _; simp only [zero_add]
    have hprod := sum_pairCorr_layerProd f hin hjn
    have hci : (Nat.choose n i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hin).ne'
    have hcj : (Nat.choose n j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjn).ne'
    have hli : (Nat.choose n i : ℝ) * layerAvg (fun x => boolToReal (f x)) i = (si : ℝ) := by
      rw [layerAvg, mul_div_cancel₀ _ hci]; exact hlayers (i, si) hmemi
    have hlj : (Nat.choose n j : ℝ) * layerAvg (fun x => boolToReal (f x)) j = (sj : ℝ) := by
      rw [layerAvg, mul_div_cancel₀ _ hcj]; exact hlayers (j, sj) hmemj
    have hterm : ((μ * (fastChoose n i : ℤ) : ℤ) : ℝ) *
        ∑ m ∈ Finset.range (tHi - tLo + 1),
          (Nat.choose i (tLo + (0 + m)) * Nat.choose (n - i) (j - (tLo + (0 + m))) : ℝ) *
            pairCorr f i j (tLo + (0 + m)) = (μ : ℝ) * ((si * sj : ℕ) : ℝ) := by
      rw [hsum_eq, hprod, fastChoose_eq]; push_cast
      calc (μ : ℝ) * (Nat.choose n i : ℝ) *
            ((Nat.choose n j : ℝ) * layerAvg (fun x => boolToReal (f x)) i *
              layerAvg (fun x => boolToReal (f x)) j)
          = (μ : ℝ) * (((Nat.choose n i : ℝ) * layerAvg (fun x => boolToReal (f x)) i) *
              ((Nat.choose n j : ℝ) * layerAvg (fun x => boolToReal (f x)) j)) := by ring
        _ = (μ : ℝ) * ((si : ℝ) * (sj : ℝ)) := by rw [hli, hlj]
    refine ⟨trivial, hwfM, ?_⟩
    dsimp only [terwStepObj, terwStepP, terwStepM]
    change ((μ * ((si * sj : ℕ) : ℤ) : ℤ) : ℝ) ≤
      IntTrie.evalTrie pVal 1 0 .empty +
      IntTrie.evalTrie (terwMVal f) 1 0
        (addHypLoop n i j tLo (μ * (fastChoose n i : ℤ)) (tHi - tLo + 1) 0 .empty)
    rw [hevM, hterm]; simp only [IntTrie.evalTrie]; push_cast; linarith
  | eqCustom idx μ =>
    simp only [terwStepOk] at hok
    cases hget : customEqs[idx]? with
    | none => simp [hget] at hok
    | some eq =>
      rcases eq with ⟨terms, rhs⟩
      have hmem : (terms, rhs) ∈ customEqs := List.mem_of_getElem? hget
      obtain ⟨hvalid_terms, heq_terms⟩ := hcustom (terms, rhs) hmem
      obtain ⟨hwfM, hevM⟩ := wellFormed_and_eval_addMList f hn μ terms .empty hvalid_terms trivial
      refine ⟨trivial, ?_, ?_⟩
      · simp [terwStepM, hget, hwfM]
      · simp only [terwStepObj, terwStepP, terwStepM, hget, hevM, heq_terms, IntTrie.evalTrie]
        push_cast; linarith
  | ubPLo k lam =>
    simp only [terwStepOk, decide_eq_true_eq] at hok
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 k 1 0 (lam : ℤ) .empty (by omega) trivial
    have hnn : 0 ≤ pVal k := layerAvg_bool_nonneg f k
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfP, trivial, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevP, IntTrie.evalTrie, zero_add, one_mul]
    push_cast; nlinarith
  | ubPHi k lam =>
    simp only [terwStepOk, decide_eq_true_eq] at hok
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 k 1 0 (-(lam : ℤ)) .empty (by omega) trivial
    have hle1 : pVal k ≤ 1 := layerAvg_bool_le_one f k hok
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfP, trivial, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevP, IntTrie.evalTrie, zero_add, one_mul]
    push_cast; nlinarith
  | ubMLo i j t lam =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t) 1 0
      (lam : ℤ) .empty (canonMKey_lt _ _ _ (by have := hvalid.1; omega)
        (by have := hvalid.2.1; omega) (by have := hvalid.1; have := hvalid.2.2.1; omega)) trivial
    have hnn : 0 ≤ pairCorr f i j t := pairCorr_nonneg f
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨trivial, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevM, IntTrie.evalTrie, zero_add, one_mul,
      terwMVal_canonMKey f hn hvalid]; push_cast; nlinarith
  | ubMHi i j t lam =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t) 1 0
      (-(lam : ℤ)) .empty (canonMKey_lt _ _ _ (by have := hvalid.1; omega)
        (by have := hvalid.2.1; omega) (by have := hvalid.1; have := hvalid.2.2.1; omega)) trivial
    have hle1 : pairCorr f i j t ≤ 1 := pairCorr_le_one f hvalid
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨trivial, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevM, IntTrie.evalTrie, zero_add, one_mul,
      terwMVal_canonMKey f hn hvalid]; push_cast; nlinarith
  | ubMLePi i j t lam =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 i 1 0 (lam : ℤ) .empty
      (by have := hvalid.1; omega) trivial
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t) 1 0
      (-(lam : ℤ)) .empty (canonMKey_lt _ _ _ (by have := hvalid.1; omega)
        (by have := hvalid.2.1; omega) (by have := hvalid.1; have := hvalid.2.2.1; omega)) trivial
    have hle_i : pairCorr f i j t ≤ pVal i := pairCorr_le_left f hvalid
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfP, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevP, hevM, IntTrie.evalTrie, zero_add, one_mul,
      terwMVal_canonMKey f hn hvalid]; push_cast; nlinarith
  | ubMLePj i j t lam =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 j 1 0 (lam : ℤ) .empty
      (by have := hvalid.2.1; omega) trivial
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t) 1 0
      (-(lam : ℤ)) .empty (canonMKey_lt _ _ _ (by have := hvalid.1; omega)
        (by have := hvalid.2.1; omega) (by have := hvalid.1; have := hvalid.2.2.1; omega)) trivial
    have hle_j : pairCorr f i j t ≤ pVal j := pairCorr_le_right f hvalid
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfP, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevP, hevM, IntTrie.evalTrie, zero_add, one_mul,
      terwMVal_canonMKey f hn hvalid]; push_cast; nlinarith
  | ubMMcc i j t lam =>
    have hvalid := (validTripleB_iff n i j t).mp hok
    obtain ⟨hwfP1, hevP1⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 i 1 0 (-(lam : ℤ)) .empty
      (by have := hvalid.1; omega) trivial
    obtain ⟨hwfP2, hevP2⟩ := IntTrie.wellFormed_and_eval_addAt pVal 5 j 1 0 (-(lam : ℤ)) _
      (by have := hvalid.2.1; omega) hwfP1
    obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_addAt (terwMVal f) 15 (canonMKey i j t) 1 0
      (lam : ℤ) .empty (canonMKey_lt _ _ _ (by have := hvalid.1; omega)
        (by have := hvalid.2.1; omega) (by have := hvalid.1; have := hvalid.2.2.1; omega)) trivial
    have hmcc : pVal i + pVal j - pairCorr f i j t ≤ 1 := pairCorr_frechet f hvalid
    have hlam : (0 : ℝ) ≤ (lam : ℝ) := Nat.cast_nonneg lam
    refine ⟨hwfP2, hwfM, ?_⟩
    simp only [terwStepObj, terwStepP, terwStepM, hevP2, hevP1, hevM, IntTrie.evalTrie, zero_add,
      one_mul, terwMVal_canonMKey f hn hvalid]; push_cast; nlinarith

/-- **Soundness of Direct Joint Terwilliger LP Bound Verifier**:
A verified pure-integer `BinTree` certificate proves
`(expectedLb : ℝ) ≤ (scale : ℝ) * (evalTargetP f targetP + evalTargetM f targetM)`. -/
theorem terw_lp_bound {n d : ℕ} (f : BooleanFun n)
    (hf : polyDegree f ≤ d)
    (hf0 : f (zeroVec n) = false)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true)
    (layerSums : List (ℕ × ℕ))
    (hlayers : ∀ p ∈ layerSums, realLayerSum (fun x => boolToReal (f x)) p.1 = (p.2 : ℝ))
    (customEqs : List (List (ℕ × ℕ × ℕ × ℤ) × ℤ))
    (hcustom : ∀ eq ∈ customEqs,
      (∀ q ∈ eq.1, ValidTriple n q.1 q.2.1 q.2.2.1) ∧ evalTargetM f eq.1 = (eq.2 : ℝ))
    (tree : BinTree TerwStep)
    (targetP : List (ℕ × ℤ)) (targetM : List (ℕ × ℕ × ℕ × ℤ))
    (scale : ℕ) (expectedLb : ℤ)
    (hcert : checkTerwLPBound n d layerSums customEqs tree targetP targetM scale expectedLb = true) :
    (expectedLb : ℝ) ≤ (scale : ℝ) * (evalTargetP f targetP + evalTargetM f targetM) := by
  unfold checkTerwLPBound at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcert
  obtain ⟨⟨⟨⟨⟨⟨hn, htp⟩, htm⟩, hok⟩, hp0⟩, hm0⟩, hlb⟩ := hcert
  let pVal : ℕ → ℝ := fun k => layerAvg (fun x => boolToReal (f x)) k
  have htree : ∀ tr : BinTree TerwStep,
      tr.all (terwStepOk n d layerSums customEqs) = true →
      IntTrie.WellFormed 5 (IntTrie.mergeTree (terwStepP n d) tr) ∧
      IntTrie.WellFormed 15 (IntTrie.mergeTree (terwStepM n customEqs) tr) ∧
      (tr.sumZ (terwStepObj customEqs) : ℝ) ≤
        IntTrie.evalTrie pVal 1 0 (IntTrie.mergeTree (terwStepP n d) tr) +
        IntTrie.evalTrie (terwMVal f) 1 0 (IntTrie.mergeTree (terwStepM n customEqs) tr) := by
    intro tr
    induction tr with
    | empty =>
      intro _
      exact ⟨trivial, trivial, by simp [BinTree.sumZ, IntTrie.mergeTree, IntTrie.evalTrie]⟩
    | leaf s =>
      intro hs
      exact terwStep_sound f hn hf hf0 hf1 layerSums hlayers customEqs hcustom s hs
    | node l r ihl ihr =>
      intro hlr
      simp only [BinTree.all, Bool.and_eq_true] at hlr
      obtain ⟨hwfPl, hwfMl, hlel⟩ := ihl hlr.1
      obtain ⟨hwfPr, hwfMr, hler⟩ := ihr hlr.2
      obtain ⟨hwfP, hevP⟩ := IntTrie.wellFormed_and_eval_merge pVal 5 1 0 _ _ hwfPl hwfPr
      obtain ⟨hwfM, hevM⟩ := IntTrie.wellFormed_and_eval_merge (terwMVal f) 15 1 0 _ _ hwfMl hwfMr
      refine ⟨hwfP, hwfM, ?_⟩
      dsimp only [BinTree.sumZ, IntTrie.mergeTree]
      rw [hevP, hevM]; push_cast; linarith
  obtain ⟨hwfP, hwfM, hle⟩ := htree tree hok
  have htp' : ∀ p ∈ targetP, p.1 ≤ n := fun p hp => by simpa using htp p hp
  have htm' : ∀ q ∈ targetM, ValidTriple n q.1 q.2.1 q.2.2.1 :=
    fun q hq => (validTripleB_iff n q.1 q.2.1 q.2.2.1).mp (htm q hq)
  obtain ⟨_, hevP⟩ := wellFormed_and_eval_addPList f hn (-(scale : ℤ)) targetP
    (IntTrie.mergeTree (terwStepP n d) tree) htp' hwfP
  obtain ⟨_, hevM⟩ := wellFormed_and_eval_addMList f hn (-(scale : ℤ)) targetM
    (IntTrie.mergeTree (terwStepM n customEqs) tree) htm' hwfM
  rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hp0] at hevP
  rw [IntTrie.evalTrie_eq_zero_of_isZero _ 1 0 _ hm0] at hevM
  have hlbR : (expectedLb : ℝ) ≤ (tree.sumZ (terwStepObj customEqs) : ℝ) := by exact_mod_cast hlb
  push_cast at hevP hevM
  dsimp only [pVal] at hle
  linarith

end DegreeSensitivity
