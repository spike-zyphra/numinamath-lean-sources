import Mathlib

theorem algebra_8045  (x: ℝ) (y: ℝ)
(h₀: 0 ≤ x - 1 / 2 ∧ 0 ≤ 1 / 2 - x)
(h₁: y = Real.sqrt (x - 1 / 2) + Real.sqrt (1 / 2 - x) + Real.sqrt 2) :
|y - 1| + Real.sqrt (y^2 - 4 * y + 4) - 3 * x = - 1 / 2 := by
  have hx1 : 0 ≤ x - 1 / 2 := h₀.1
  have hx2 : 0 ≤ 1 / 2 - x := h₀.2
  have hx : x = 1 / 2 := by linarith
  rw [hx] at h₁
  have hy : y = Real.sqrt 2 := by
    rw [h₁]
    norm_num
    all_goals
      simp [Real.sqrt_zero]
  rw [hy, hx]
  have h2 : Real.sqrt 2 ≥ 1 := by
    have h3 : Real.sqrt 1 = 1 := Real.sqrt_one
    have h4 : Real.sqrt 2 ≥ Real.sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
    linarith [h3]
  have h3 : |Real.sqrt 2 - 1| = Real.sqrt 2 - 1 := by
    rw [abs_of_nonneg]
    linarith
    all_goals nlinarith [Real.sqrt_nonneg 2, h2]
  have h4 : Real.sqrt (Real.sqrt 2 ^ 2 - 4 * Real.sqrt 2 + 4) = 2 - Real.sqrt 2 := by
    have h5 : Real.sqrt 2 ^ 2 - 4 * Real.sqrt 2 + 4 = (Real.sqrt 2 - 2) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h5]
    have h6 : Real.sqrt ((Real.sqrt 2 - 2) ^ 2) = |Real.sqrt 2 - 2| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h6]
    have h7 : Real.sqrt 2 < (2 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [abs_of_neg (by linarith [h7]) ]
    all_goals linarith
  rw [h3, h4]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]