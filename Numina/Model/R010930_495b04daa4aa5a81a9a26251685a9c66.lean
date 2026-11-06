import Mathlib

theorem algebra_203112 {a : ℕ → ℤ} (ha : a 1 > 1)
    (h : ∀ n, a (n + 1) = 2 * a n - 1) :
    ∑ i in Finset.range n, a (i + 1) = (a 1 - 1) * (2 ^ n - 1) + n := by
  -- First prove the formula for `a n`.
  have h1 : ∀ (k : ℕ), a (k + 1) = 1 + (a 1 - 1) * (2 ^ k) := by
    intro k 
    induction k with 
    | zero => 
      norm_num 
    | succ k ih => 
      have eq1 : a (k + 2) = 2 * a (k + 1) - 1 := by 
        specialize h (k + 1)
        simpa using h 
      rw [eq1] 
      rw [ih]
      simp [pow_add, pow_mul]
      ring

  -- Prove the formula for the sum.
  have eq2 : ∀ (n : ℕ), ∑ i in Finset.range n, a (i + 1) = (a 1 - 1) * (2 ^ n - 1) + n := by
    intro n 
    induction n with 
    | zero => 
      simp 
    | succ n ih => 
      rw [Finset.sum_range_succ, ih]
      have eq3 : a (n + 1) = 1 + (a 1 - 1) * (2 ^ n) := by 
        specialize h1 n 
        simpa using h1 
      rw [eq3]
      simp [pow_add, pow_mul]
      all_goals 
        ring_nf 
  exact eq2 n