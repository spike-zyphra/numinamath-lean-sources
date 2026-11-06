import Mathlib

theorem algebra_108835 {a p m : ℝ} (ha : a ≠ 0) (hp : p > 0)
    (h : ∀ x y, y = a * x ^ 2 - 3 * x + 3 → x = y ^ 2 / (2 * p) + m) :
    a * p * m = -3 := by

  have eq1 := h 0 3 (by 
    ring
  )
  have eq1' : (0 : ℝ) = (3 : ℝ) ^ 2 / (2 * p) + m := by 
    simpa using eq1
  have eq2 : m = -9 / (2 * p) := by
    field_simp [(show (2 * p) ≠ 0 by nlinarith)] at eq1' ⊢
    nlinarith
  
  have eq3 := h 1 a (by 
    ring
  )
  have eq3' : (1 : ℝ) = (a : ℝ) ^ 2 / (2 * p) + m := by 
    simpa using eq3
  have eq4 : a ^ 2 = 2 * p + 9 := by 
    rw [eq2] at eq3'
    field_simp [(show (2 * p) ≠ 0 by nlinarith)] at eq3' ⊢
    nlinarith
  
  have eq5 := h 2 (4 * a - 3) (by 
    ring
  )
  have eq5' : (2 : ℝ) = (4 * a - 3) ^ 2 / (2 * p) + m := by 
    simpa using eq5
  rw [eq2] at eq5'
  field_simp [(show (2 * p) ≠ 0 by nlinarith)] at eq5' ⊢
  nlinarith [sq_nonneg (a - 3 / 7), sq_nonneg (p - 9 / 7), sq_nonneg (a * (a - (6 / 7) * p + 12 / 7)), sq_pos_of_ne_zero ha, sq_pos_of_pos hp, sq_nonneg (a ^ 2 - 49 / 16)]