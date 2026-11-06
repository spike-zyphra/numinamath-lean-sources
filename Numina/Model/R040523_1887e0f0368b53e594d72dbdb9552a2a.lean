import Mathlib

theorem algebra_610682 {a r : ℝ } (hr : abs r < 1) (h1 : 10 = a / (1 - r)) (h2 : 15 = (a + 4) / (1 - r)): r = 1/5  := by
  have h3 : 1 - r ≠ 0 := by
    by_contra h
    have h4 : r = 1 := by linarith
    have h5 : abs r ≥ 1 := by
      rw [h4]
      norm_num
    linarith
  have eq1 : a = 10 * (1 - r) := by
    have h3' : 1 - r ≠ 0 := h3
    field_simp [h3'] at h1 ⊢
    linarith
  have eq2 : 15 * (1 - r) = a + 4 := by
    have h3' : 1 - r ≠ 0 := h3
    field_simp [h3'] at h2 ⊢
    linarith
  rw [eq1] at eq2
  have eq3 : 15 * (1 - r) = 10 * (1 - r) + 4 := by
    linarith
  have eq4 : 5 * (1 - r) = 4 := by
    linarith
  have eq5 : 1 - r = 4 / 5 := by
    linarith
  linarith