import Mathlib

theorem algebra_109071 (x : ℝ) (hx : x > 0) (h : 80 / x = 40 / (x + 5)) :
    7 + 3 / 11 ≤ x ∧ x < 8 + 8 / 9 := by 
  have hx1 : x + 5 > 0 := by nlinarith
  have h1 : x ≠ 0 := by nlinarith
  have h2 : x + 5 ≠ 0 := by nlinarith
  have h3 : 80 * (x + 5) = 40 * x := by
    field_simp [h1, h2] at h
    nlinarith
  have h_eq : x = -10 := by
    nlinarith
  linarith