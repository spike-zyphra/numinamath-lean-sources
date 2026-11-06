import Mathlib

theorem algebra_122536 {x y : ℝ} (h₀ : x + x * y + y = 2 + 3 * Real.sqrt 2) (h₁ : x ^ 2 + y ^ 2 = 6) :
    (x = 2 ∧ y = Real.sqrt 2) ∨ (x = Real.sqrt 2 ∧ y = 2) := by
  have h2 : (x + y) + (x * y) = 2 + 3 * Real.sqrt 2 := by
    nlinarith
  have h3 : (x + y) ^ 2 - 2 * (x * y) = 6 := by
    nlinarith [h₁]
  -- Substitute `S = x+y` and `P = x*y`.
  have h4 : (x + y) ^ 2 + 2 * (x + y) - 10 - 6 * Real.sqrt 2 = 0 := by
    have h5 : (x * y) = (2 + 3 * Real.sqrt 2) - (x + y) := by
      linarith [h2]
    rw [h5] at h3
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg ( (x + y) - (2 + Real.sqrt 2)), sq_nonneg ( (x + y) - (-4 - Real.sqrt 2))]
  have h6 : (x + y - (2 + Real.sqrt 2)) * (x + y - (-4 - Real.sqrt 2)) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg ( (x + y) - (2 + Real.sqrt 2)), sq_nonneg ( (x + y) - (-4 - Real.sqrt 2))]
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case `x + y = 2 + Real.sqrt 2`:
    have h8 : x + y = 2 + Real.sqrt 2 := by
      nlinarith
    have h9 : x * y = 2 * Real.sqrt 2 := by
      nlinarith [h2, h8, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    have h10 : (x - 2) * (x - Real.sqrt 2) = 0 := by
      have h11 : y = (2 + Real.sqrt 2) - x := by linarith
      rw [h11] at h9
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case `x = 2`:
      left
      have hx : x = 2 := by linarith
      have hy : y = Real.sqrt 2 := by 
        nlinarith [h8, hx, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      exact ⟨hx, hy⟩
    · -- Case `x = Real.sqrt 2`:
      right
      have hx : x = Real.sqrt 2 := by linarith
      have hy : y = 2 := by 
        nlinarith [h8, hx, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      exact ⟨hx, hy⟩
  · -- Case `x + y = -4 - Real.sqrt 2`:
    have h8 : x + y = -4 - Real.sqrt 2 := by
      nlinarith
    have h9 : x * y = 6 + 4 * Real.sqrt 2 := by
      nlinarith [h2, h8, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 4 + Real.sqrt 2), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x * y - (6 + 4 * Real.sqrt 2))]