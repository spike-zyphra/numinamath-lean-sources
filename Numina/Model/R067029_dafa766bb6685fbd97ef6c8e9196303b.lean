import Mathlib

theorem algebra_298036 {a b c : ℝ} (h : 1 / 4 * (b - c)^2 = (a - b) * (c - a)) (ha : a ≠ 0) :
    (b + c) / a = 2 := by
  have h1 : (b + c - 2 * a) ^ 2 = 0 := by 
    nlinarith
  have h2 : b + c - 2 * a = 0 := by 
    apply pow_eq_zero 
    exact h1
  have h3 : b + c = 2 * a := by linarith
  field_simp [ha]
  all_goals nlinarith