import Mathlib

theorem algebra_172 {a b : ℝ} (hab : a * b ≠ 1) (ha : 5 * a ^ 2 + 2001 * a + 9 = 0) (hb : 9 * b ^ 2 + 2001 * b + 5 = 0) : a / b = 9 / 5 := by
  have hbne : b ≠ 0 := by
    by_contra h
    rw [h] at hb
    nlinarith
  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    nlinarith
  have eq2 : (5 * a ^ 2 + 9) * b = (9 * b ^ 2 + 5) * a := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (5 * a - 9 * b), sq_nonneg (a - b)]
  have eq3 : (a * b - 1) * (5 * a - 9 * b) = 0 := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (5 * a - 9 * b), sq_nonneg (a - b)]
  cases' (mul_eq_zero.1 eq3) with eq4 eq5
  · -- ab - 1 = 0, so ab = 1
    have eq5 : a * b = 1 := by linarith
    exfalso
    apply hab
    linarith
  · -- 5a - 9b = 0
    have eq6 : 5 * a = 9 * b := by linarith
    field_simp [hbne]
    linarith