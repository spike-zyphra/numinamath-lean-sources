import Mathlib

theorem algebra_606015 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x^3 + y^3 + 3 * x^2 * y^2 = x^3 * y^3) :
    1 / x + 1 / y = -2 ∨ 1 / x + 1 / y = 1 := by 
  have eq1 : (x + y) ^ 3 - 3 * (x + y) * (x * y) + 3 * (x * y) ^ 2 = (x * y) ^ 3 := by
    nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show y ≠ 0 by exact hy)]
  have eq2 : (x + y) ^ 3 - 3 * (x + y) * (x * y) + 3 * (x * y) ^ 2 - (x * y) ^ 3 = 0 := by linarith
  have eq3 : ((x + y) - (x * y)) * ((x + y) ^ 2 + (x + y) * (x * y) + (x * y) ^ 2 - 3 * (x * y)) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show y ≠ 0 by exact hy)]
  cases' (mul_eq_zero.mp eq3) with h1 h2
  · -- Case where $h1 : (x + y) - x * y = 0$
    right
    have eq4 : 1 / x + 1 / y = 1 := by
      have h3 : x + y = x * y := by linarith
      have h5 : x * y ≠ 0 := by
        apply mul_ne_zero
        exact hx
        exact hy
      have eq6 : 1 / x + 1 / y = (x + y) / (x * y) := by
        field_simp
        all_goals
        ring
      rw [eq6]
      rw [show x + y = x * y by linarith]
      field_simp [show x * y ≠ 0 by exact h5]
    exact eq4
  · -- Case where $h2 : (x + y) ^ 2 + (x + y) * (x * y) + (x * y) ^ 2 - 3 * (x * y) = 0$
    left
    have eq4 : (x + y) = -2 * (x * y) := by
      nlinarith [sq_nonneg ((x * y) ^ 2), sq_nonneg ((x + y) ^ 2), sq_nonneg ((x + y) + 2 * (x * y)), sq_nonneg ((x + y) - (-2 * (x * y))), sq_nonneg ((x - y) ^ 2), sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show y ≠ 0 by exact hy)]
    have eq5 : 1 / x + 1 / y = -2 := by
      have eq6 : 1 / x + 1 / y = (x + y) / (x * y) := by
        field_simp
        all_goals
        ring
      rw [eq6]
      rw [show x + y = -2 * (x * y) by linarith]
      have h5 : x * y ≠ 0 := by
        apply mul_ne_zero
        exact hx
        exact hy
      field_simp [h5]
    exact eq5