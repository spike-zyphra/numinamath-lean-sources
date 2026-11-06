import Mathlib

theorem algebra_236945 {x y : ℝ} (h₁ : x + x * y + y = 2 + 3 * √2) (h₂ : x ^ 2 + y ^ 2 = 6) :
    (x = 2 ∧ y = √2) ∨ (x = √2 ∧ y = 2) := by

  have eq3 : (x + y) + (x * y) = 2 + 3 * √2 := by
    nlinarith
  have eq4 : (x + y) ^ 2 - 2 * (x * y) = 6 := by
    nlinarith
  have h3 : (x + y) = 2 + Real.sqrt 2 ∨ (x + y) = -4 - Real.sqrt 2 := by
    have eq5 : (x + y) ^ 2 + 2 * (x + y) - 10 - 6 * Real.sqrt 2 = 0 := by
      nlinarith [sq_nonneg (x - y), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    have eq6 : ((x + y) - (2 + Real.sqrt 2)) * ((x + y) - (-4 - Real.sqrt 2)) = 0 := by
      nlinarith [sq_nonneg (x + y +4 + Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    cases' (mul_eq_zero.1 eq6) with h5 h6
    · 
      left
      linarith
    · 
      right
      linarith
  rcases h3 with h4 | h4
  · -- Case where x + y = 2 + Real.sqrt 2.
    have eq5 : x * y = 2 * Real.sqrt 2 := by
      nlinarith [h4, eq3, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    have h5 : (x - 2) * (x - Real.sqrt 2) = 0 := by
      have h6 : y = (2 + Real.sqrt 2) - x := by
        nlinarith [h4, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      rw [h6] at eq5 eq3
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case where x - 2 =0.
      have hx : x = 2 := by linarith
      have hy : y = Real.sqrt 2 := by
        nlinarith [h4, hx, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      left
      exact ⟨hx, hy⟩
    · -- Case where x - Real.sqrt 2 =0.
      have hx : x = Real.sqrt 2 := by linarith
      have hy : y = 2 := by
        nlinarith [h4, hx, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      right
      exact ⟨hx, hy⟩
  · -- Case where x + y = -4 - Real.sqrt 2.
    -- This case leads to a contradiction as the discriminant is negative.
    have eq5 : x * y = 6 + 4 * Real.sqrt 2 := by
      nlinarith [h4, eq3, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y +4 + Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x - 2), sq_nonneg (y - Real.sqrt 2)]