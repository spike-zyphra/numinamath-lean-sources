import Mathlib

theorem algebra_37733 (x y : ℝ) (h₀ : y = x + 2) (h₁ : 1 < y ∧ y < 3) :
  √(y ^ 2 - 8 * x) + √(y ^ 2 + 2 * x + 5) = 5 := by
  have hx : x = y - 2 := by linarith [h₀]
  have h2 : y ^ 2 - 8 * x = (y - 4) ^ 2 := by
    rw [hx]
    linarith
  have h3 : y ^ 2 + 2 * x + 5 = (y + 1) ^ 2 := by
    rw [hx]
    linarith
  have h4 : √(y ^ 2 - 8 * x) = |y - 4| := by
    rw [h2]
    have h5 : (y - 4 : ℝ) ^ 2 ≥ 0 := sq_nonneg (y - 4)
    rw [Real.sqrt_sq_eq_abs]
  have h6 : √(y ^ 2 + 2 * x + 5) = |y + 1| := by
    rw [h3]
    have h7 : (y + 1 : ℝ) ^ 2 ≥ 0 := sq_nonneg (y + 1)
    rw [Real.sqrt_sq_eq_abs]
  have h8 : |y - 4| = 4 - y := by
    rw [abs_of_neg]
    linarith
    all_goals linarith
  have h9 : |y + 1| = y + 1 := by 
    rw [abs_of_pos]
    linarith
    all_goals linarith
  rw [h4, h6, h8, h9]
  linarith