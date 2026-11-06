import Mathlib

theorem algebra_189975 (d v : ℝ) (h : d > 0) (h1 : v > 0) (h2 : d / v = d / (v * (1 + 1 / 4)) + 1)
    (h3 : d / v = (d - 150) / (v * (1 + 1 / 5)) + 40 / 60) :
    d = 750 := by
  have eq1 : d = 5 * v := by
    have h2' : d / v = d / (v * (1 + 1 / 4)) + 1 := h2
    have pos1 : v ≠ 0 := by linarith
    field_simp [show v * (1 + 1 / 4 : ℝ) ≠ 0 by
      apply mul_ne_zero
      exact pos1
      norm_num] at h2'
    nlinarith
  have h3' : d / v = (d - 150) / (v * (1 + 1 / 5)) + 40 / 60 := h3
  rw [show d = 5 * v by linarith [eq1]] at h3'
  have pos2 : v ≠ 0 := by linarith
  field_simp [show v * (1 + 1 / 5 : ℝ) ≠ 0 by
    apply mul_ne_zero
    exact pos2
    norm_num] at h3'
  nlinarith [show d = 5 * v by linarith [eq1], show v > 0 by linarith]