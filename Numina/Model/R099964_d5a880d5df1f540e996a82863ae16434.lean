import Mathlib

theorem number_theory_8569 (a : ℕ → ℤ) (ha1 : a 1 = 2)
    (han : ∀ n, a (n + 1) = a n ^ 3 - a n + 1) :
    ∀ n p, 0 < n → Odd p → Prime p → p ∣ a n → n < p := by 
  -- For n = 0 in recurrence: `a 1 = a 0 ^ 3 - a 0 + 1`, and a 1 is given as 2
  have h0 := han 0
  rw [ha1] at h0 
  norm_num at h0 
  -- Let's derive h2: `a 0 ^ 3 - a 0 - 1 = 0`, to prove that it's contradictory to given conditions
  have h2 : a 0 ^ 3 - a 0 - 1 = 0 := by linarith 
  have h3 : a 0 ^ 3 - a 0 - 1 ≠ 0 := by 
    have h5 : a 0 ≤ 1 := by
      nlinarith [sq_nonneg (a 0 ^ 2 - 1 : ℤ), sq_nonneg (a 0 : ℤ), sq_nonneg (a 0 + 1 : ℤ), sq_nonneg (a 0 - 1 : ℤ)]
    have h6 : a 0 ≥ -1 := by 
      nlinarith [sq_nonneg (a 0 ^ 2 - 1 : ℤ), sq_nonneg (a 0 : ℤ), sq_nonneg (a 0 + 1 : ℤ), sq_nonneg (a 0 - 1 : ℤ)]
    interval_cases a 0 <;> omega 
  contradiction