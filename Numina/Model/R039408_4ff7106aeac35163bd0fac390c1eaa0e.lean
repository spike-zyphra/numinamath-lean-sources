import Mathlib

theorem algebra_120749 {x y : ℝ} (h1 : x + x * y + y = 2 + 3 * Real.sqrt 2) (h2 : x ^ 2 + y ^ 2 = 6) :
    (x = 2 ∧ y = Real.sqrt 2) ∨ (x = Real.sqrt 2 ∧ y = 2) := by
  have h3 : (x + y) + x * y = 2 + 3 * Real.sqrt 2 := by
    nlinarith
  have h4 : (x + y) ^ 2 - 2 * (x * y) = 6 := by
    nlinarith [h2]
  have h7 : ((x + y) - (2 + Real.sqrt 2)) * ((x + y) - (-4 - Real.sqrt 2)) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg ((x + y) - (2 + Real.sqrt 2)), sq_nonneg ((x + y) - (-4 - Real.sqrt 2)), sq_nonneg (x - y), sq_nonneg (x + y + 4 + Real.sqrt 2)]
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- Case s = 2 + Real.sqrt 2
    have h8' : x + y = 2 + Real.sqrt 2 := by linarith
    have h10 : x * y = 2 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h11 : (x - 2) * (x - Real.sqrt 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- Case x = 2
      have hx : x = 2 := by linarith
      have hy : y = Real.sqrt 2 := by
        nlinarith
      left
      exact ⟨hx, hy⟩
    · -- Case x = Real.sqrt 2
      have hx : x = Real.sqrt 2 := by
        nlinarith
      have hy : y = 2 := by
        nlinarith
      right
      exact ⟨hx, hy⟩
  · -- Case s = -4 - Real.sqrt 2
    have h9' : x + y = -4 - Real.sqrt 2 := by linarith
    have h10 : x * y = 6 + 4 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith [sq_nonneg (x - y), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x + y + 4 + Real.sqrt 2)]