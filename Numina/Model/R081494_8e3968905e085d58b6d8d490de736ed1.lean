import Mathlib

theorem algebra_228136 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 2 * (a * b + b * c + a * c)) :
    1 / a + 1 / b + 1 / c = 1 / 2 := by
  have h1 : a * b * c = 2 * (a * b + b * c + a * c) := h

  have h2 : 1 / a + 1 / b + 1 / c = (a * b + b * c + a * c) / (a * b * c) := by
    field_simp
    ring

  have h3 : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    all_goals linarith
  have h4 : a * b + b * c + a * c = (a * b * c) / 2 := by 
    nlinarith
  
  have fraction_eq : (a * b + b * c + a * c) / (a * b * c) = 1 / 2 := by 
    have non_zero : a * b * c ≠ 0 := h3
    have eq1 : a * b + b * c + a * c = (a * b * c) / 2 := h4
    field_simp
    nlinarith

  linarith [h2, fraction_eq]