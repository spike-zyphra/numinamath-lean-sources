import Mathlib

theorem inequalities_597020 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + 2 * b = 1) :
    9 ≤ 1 / a + 2 / b := by
  have h1 : 0 < b := hb
  have h2 : a ≠ 0 := by linarith
  have h3 : b ≠ 0 := by linarith
  have h6 : 1 / a + 2 / b - 9 ≥ 0 := by
    have h7 : 0 < a * b := mul_pos ha hb
    have h8 : 1 / a + 2 / b - 9 = (b + 2 * a - 9 * (a * b)) / (a * b) := by
      field_simp
      <;> ring
    rw [h8]
    have hb_eq : b = (1 - a) / 2 := by linarith
    have h9 : b + 2 * a - 9 * (a * b) ≥ 0 := by
      rw [hb_eq]
      nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (a - b), sq_nonneg (a * b)]
    apply div_nonneg
    linarith
    positivity
  linarith