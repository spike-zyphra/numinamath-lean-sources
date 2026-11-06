import Mathlib

open Finset Nat Real

-- Show that a is positive
lemma l_a_pos  {a : ℕ → ℚ} (n : ℕ) (ha1 : a 0 = 1) (ha2 : a 1 = 2)
    (han : ∀ n ≥ 2, a n = a (n - 1) + a (n - 2)) :
    0 < a n := by
  -- Use induction
  induction n using twoStepInduction with
  -- Trivial
  | zero => aesop
  -- Trivial
  | one => aesop
  -- Easy from previous cases
  | more k ih ih' =>
    rw [han (k + 2) (by linarith)]
    aesop
    linarith
-- Show that every term is bounded between multiples of the previous term
lemma l_bound {a : ℕ → ℚ} {n : ℕ} (ha1 : a 0 = 1) (ha2 : a 1 = 2)
    (han : ∀ n ≥ 2, a n = a (n - 1) + a (n - 2)) :
    3/2 * a n ≤ a (n + 1) ∧ a (n + 1) ≤ 2 * a n := by
  -- Use induction
  induction n using twoStepInduction with
  -- Zero case follows from initial values
  | zero =>
    rw [ha1, ha2]
    norm_num
  -- One case follows from initial values
  | one => aesop <;> norm_num
  -- Induction step
  | more k ih ih' =>
    constructor
    · -- Prove lower bound
      rw [han (k + 2 + 1) (by linarith)]
      norm_num at ih'
      norm_num
      conv in k + 2 + 1 - 2 =>
        rw [add_assoc, add_comm 2, ← add_assoc]
        simp
      -- Use the upper bound to bound previous term
      have : 1 / 2 * a (k + 2) ≤ a (k + 1) := by
        rcases ih' with ⟨ih', ih''⟩
        conv at ih' in k + 1 + 1 =>
          rw [add_assoc]
          simp
        linarith
      -- Use the previous term bound to rewrite in terms of a (k + 2)
      calc
        a (k + 2) + a (k + 1) ≥ a (k + 2) + 1 / 2 * a (k + 2) := by gcongr
        _ = 3 / 2 * a (k + 2) := by linarith
    -- Prove upper bound
    rw [add_assoc, add_comm 2, ← add_assoc, han _ (by linarith)]
    norm_num
    calc
      a (k + 2) + a (k + 1) ≤ a (k + 2) + a (k + 2) := by gcongr; rw [han (k + 2) (by linarith)]; norm_num; linarith
      _ = 2 * a (k + 2) := by linarith

/- Let's interpret the sequence $a_{n}$ as follows:


$$

a_{1}=1 ; \quad a_{2}=2 ; \quad a_{n}=a_{n-1}+a_{n-2}, \quad \text { if } \quad n \geq 3

$$


Prove that for all $n$ and $k$ (where $n, k \geq 1$ are integers),


$$

\left|\frac{a_{n+1}}{a_{n}}-\frac{a_{k+1}}{a_{k}}\right| \leq 1

$$
 -/
theorem inequalities_169123 {a : ℕ → ℚ} (ha1 : a 0 = 1) (ha2 : a 1 = 2)
    (han : ∀ n ≥ 2, a n = a (n - 1) + a (n - 2)) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    |(a (n + 1)) / a n - (a (k + 1)) / a k| ≤ 1 := by
  let q := a (n + 1) / a n
  let r := a (k + 1) / a k
  have n_bound : _ := @l_bound a n ha1 ha2 han
  have k_bound : _ := @l_bound a k ha1 ha2 han
  have : 3 / 2 ≤ a (n + 1) / a n ∧ a (n + 1) / a n ≤ 2 := by
    constructor
    · -- Prove lower bound
      rw [le_div_iff₀ (l_a_pos n ha1 ha2 han)]
      tauto
    -- Prove upper bound
    rw [div_le_iff₀ (l_a_pos n ha1 ha2 han)]
    tauto
  have : 3 / 2 ≤ a (k + 1) / a k ∧ a (k + 1) / a k ≤ 2 := by
    constructor
    · -- Prove lower bound
      rw [le_div_iff₀ (l_a_pos k ha1 ha2 han)]
      tauto
    -- Prove upper bound
    rw [div_le_iff₀ (l_a_pos k ha1 ha2 han)]
    tauto
  calc
    |a (n + 1) / a n - a (k + 1) / a k| ≤ |a (n + 1) / a n - 3 / 2| + |3 / 2 - a (k + 1) / a k| := abs_sub_le _ _ _
    _ ≤ 1/2 + 1/2 := by
      gcongr
      · rw [abs_eq_self.mpr (by linarith)]
        linarith
      rw [abs_sub_comm, abs_eq_self.mpr (by linarith)]
      linarith
    _ = 1 := by norm_num