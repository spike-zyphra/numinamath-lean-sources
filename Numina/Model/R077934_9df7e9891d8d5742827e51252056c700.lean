import Mathlib

theorem algebra_287750 {x : ℝ} (hx : x^2 - 15 * x + 1 = 0) :
    x^4 + 1 / x^4 = 49727 := by
  have hx1 : x ≠ 0 := by
    by_contra h
    rw [h] at hx
    nlinarith
  have h1 : x + 1 / x = 15 := by
    have h2 : x ≠ 0 := hx1
    field_simp at *
    nlinarith
  have h2 : x^2 + 1 / x^2 = 223 := by
    have h3 : x ≠ 0 := hx1
    have h4 : x^2 + 1 / x^2 = (x + 1 / x) ^ 2 - 2 := by
      field_simp
      ring
    rw [h4, h1]
    all_goals norm_num
  have h3 : x^4 + 1 / x^4 = 49727 := by
    have h4 : x ≠ 0 := hx1
    have h5 : x^4 + 1 / x^4 = (x^2 + 1 / x^2) ^ 2 - 2 := by
      field_simp
      ring
    rw [h5, h2]
    all_goals norm_num
  exact h3