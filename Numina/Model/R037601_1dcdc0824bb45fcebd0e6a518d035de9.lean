import Mathlib

theorem algebra_104225 (x y : ℝ) (hpos : 0 ≤ 18 * x - x^2 - 81) (hx : x^2 - y^4 = √(18 * x - x^2 - 81)) :
    (x, y) = (9, 3) ∨ (x, y) = (9, -3) := by 
  have h1 : (x - 9) ^ 2 ≤ 0 := by
    nlinarith [hpos]
  have hx9 : x = 9 := by 
    nlinarith [pow_two_nonneg (x - 9), h1]
  have h_eq : √(18 * x - x^2 - 81) = 0 := by
    rw [hx9]
    rw [Real.sqrt_eq_zero']
    norm_num
    all_goals
      norm_num
  rw [h_eq] at hx
  rw [hx9] at hx
  have hy : y^4 = 81 := by
    nlinarith
  have hy2 : y^2 = 9 := by 
    nlinarith [sq_nonneg (y^2 - 9), sq_nonneg (y + 3), sq_nonneg (y - 3)]
  have hy3 : y = 3 ∨ y = -3 := by
    have : y^2 = 9 := hy2
    have h1 : y = 3 ∨ y = -3 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      norm_num
      linarith
    exact h1
  rcases hy3 with (hy3 | hy3)
  · -- Case where y = 3
    left 
    simp [hx9, hy3]
  · -- Case where y = -3
    right 
    simp [hx9, hy3]