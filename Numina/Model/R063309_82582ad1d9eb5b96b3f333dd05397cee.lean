import Mathlib

theorem algebra_176508 (v : ℝ) (h : v > 0) (h1 : 33 / v = 6 / v + 2 * 6 / (v + 1.5)) (h2 : 81 / v = 7 / v + 20 * 6 / (v + 1.5)) :
    v = 3 := by
  have h4 : v ≠ 0 := by linarith
  have h3 : v + 1.5 ≠ 0 := by
    nlinarith
  have eq1 : 33 * (v + 1.5) = 6 * (v + 1.5) + 12 * v := by
    field_simp [h4, h3] at h1
    nlinarith
  nlinarith