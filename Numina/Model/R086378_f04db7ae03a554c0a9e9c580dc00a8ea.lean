import Mathlib

theorem algebra_237940 (d v : ℝ) (h : d > 0) (h1 : v > 0) (h2 : d / (v + 5) = 3) (h3 : d / (v - 5) = 4) :
    d = 120 := by
  have h4 : v + 5 ≠ 0 := by
    by_contra h5
    have h6 : v + 5 = 0 := by linarith
    rw [h6] at h2
    norm_num at h2
    all_goals linarith
  have h5 : v - 5 ≠ 0 := by
    by_contra h6
    have h7 : v - 5 = 0 := by linarith
    rw [h7] at h3
    norm_num at h3
    all_goals linarith
  have eq1 : d = 3 * (v + 5) := by
    have h8 : v + 5 ≠ 0 := h4
    field_simp [h8] at h2
    linarith
  have eq2 : d = 4 * (v - 5) := by
    have h9 : v - 5 ≠ 0 := h5
    field_simp [h9] at h3
    linarith
  have hv : v = 35 := by
    linarith [eq1, eq2]
  rw [hv] at eq1
  linarith