import Mathlib

theorem algebra_256336 : ∃ n : ℤ, Real.sqrt (4 - 2 * Real.sqrt 3) - (Real.sqrt 3 + 1) / (Real.sqrt 3 - 1) = n := by 
  use -3
  have h1 : Real.sqrt (4 - 2 * Real.sqrt 3) = Real.sqrt 3 - 1 := by
    have h2 : 0 ≤ Real.sqrt 3 - 1 := by
      have h3 : 1 < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h4 : Real.sqrt 3 > 1 := by linarith
      linarith
    have h5 : (Real.sqrt 3 - 1) ^ 2 = 4 - 2 * Real.sqrt 3 := by
      have h6 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [Real.sqrt_nonneg 3]
    rw [← h5]
    field_simp [Real.sqrt_sq, h2]
    all_goals nlinarith [Real.sqrt_nonneg 3]
  have h7 : (Real.sqrt 3 + 1) / (Real.sqrt 3 - 1) = 2 + Real.sqrt 3 := by
    have h8 : Real.sqrt 3 - 1 ≠ 0 := by
      have h9 : 1 < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h10 : Real.sqrt 3 > 1 := by linarith
      linarith
    field_simp [h8]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  rw [h1, h7]
  ring_nf
  <;> norm_num <;> ring