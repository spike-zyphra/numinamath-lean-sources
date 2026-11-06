import Mathlib

theorem algebra_5818 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, (a * x ^ 2 + b * x + c) = (∫ x in (0)..2, (a * x ^ 2 + b * x + c)) * x ^ 2 + (∫ x in (0)..1, (a * x ^ 2 + b * x + c)) * x + (∫ x in (0)..3, (a * x ^ 2 + b * x + c)) + 2) :
    a * 3 ^ 2 + b * 3 + c = -30 / 13 := by

  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 : ∫ x in (0)..2, (a * x ^ 2 + b * x + c) = 8 * a / 3 + 2 * b + 2 * c := by
    simp [intervalIntegral.integral_const, add_mul, mul_add, mul_comm a, mul_comm b, mul_comm c]
    field_simp
    ring
  have eq6 : ∫ x in (0)..1, (a * x ^ 2 + b * x + c) = a / 3 + b / 2 + c := by
    simp [intervalIntegral.integral_const, add_mul, mul_add, mul_comm a, mul_comm b, mul_comm c]
    field_simp
    ring
  have eq7 : ∫ x in (0)..3, (a * x ^ 2 + b * x + c) = 9 * a + 9 * b / 2 + 3 * c := by
    simp [intervalIntegral.integral_const, add_mul, mul_add, mul_comm a, mul_comm b, mul_comm c]
    field_simp
    ring
  simp [eq5, eq6, eq7] at eq1 eq2 eq3 eq4 ⊢
  ring_nf at eq1 eq2 eq3 eq4 ⊢
  nlinarith