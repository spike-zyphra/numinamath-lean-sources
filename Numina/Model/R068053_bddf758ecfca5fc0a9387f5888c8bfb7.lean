import Mathlib

theorem algebra_287669 (x y : ℝ) (hx : x = 33) (hy : y ≠ 0)
    (h : (x + y * 0.5) / (x + y) = 0.8) :
    (x + y) * 0.2 = 11 := by
  have h1 : x + y ≠ 0 := by
    by_contra h2
    have h3 : x + y = 0 := by linarith
    rw [h3] at h
    simp [hx] at h
    all_goals norm_num at h
    all_goals linarith
  have h2 : x + y ≠ 0 := h1
  have eq1 : x + y * 0.5 = 0.8 * (x + y) := by
    have h4 : x + y ≠ 0 := h2
    field_simp [h4] at h
    linarith
  rw [hx] at eq1
  ring_nf at eq1
  have hy_eq : y = 22 := by
    linarith
  rw [hx, hy_eq]
  norm_num