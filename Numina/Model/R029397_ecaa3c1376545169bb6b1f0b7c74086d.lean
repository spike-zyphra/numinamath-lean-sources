import Mathlib
theorem algebra_94620 {x : ℝ} (hx : x ≠ 0) (h : (1 - 20 / 100) * (1 + 7.5 / 100) * x = 43) : x = 50 := by
  have eq1 : (1 - 20 / 100 : ℝ) * (1 + 7.5 / 100) * x = 0.86 * x := by
    ring_nf
  rw [eq1] at h
  have h1 : x = (43 : ℝ) / (0.86 : ℝ) := by
    field_simp [(show (0.86 : ℝ) ≠ 0 by norm_num)]
    linarith
  rw [h1]
  norm_num