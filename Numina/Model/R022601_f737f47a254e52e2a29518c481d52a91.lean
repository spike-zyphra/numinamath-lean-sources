import Mathlib

theorem algebra_3741 {x y : ℝ} (h₀ : x - 3 / (y - 2) = 8) (h₁ : 2 * x - 9 / (y - 2) = 15) :
    y = 5 := by
  have hy2 : y - 2 ≠ 0 := by
    by_contra h
    have h2 : y = 2 := by linarith
    rw [h2] at h₀ h₁
    norm_num at h₀ h₁
    all_goals try { linarith }
  have eq1 : (x - 8) * (y - 2) = 3 := by
    have h2 : y - 2 ≠ 0 := hy2
    have eq1 : x - 3 / (y - 2) = 8 := h₀
    field_simp [h2] at eq1
    linarith
  have eq2 : (2 * x - 15) * (y - 2) = 9 := by
    have h2 : y - 2 ≠ 0 := hy2
    have eq2 : 2 * x - 9 / (y - 2) = 15 := h₁
    field_simp [h2] at eq2
    linarith
  have eq5 : (x - 8) * (y - 2) = 3 := eq1
  have eq7 : 2 * ((x - 8) * (y - 2)) + (y - 2) = 9 := by
    have eq8 : (2 * x - 15) * (y - 2) = 2 * ((x - 8) * (y - 2)) + (y - 2) := by
      have h2 : (2 * x - 15) = 2 * (x - 8) + 1 := by
        nlinarith
      rw [h2]
      all_goals ring
    linarith [eq8, eq2]
  have eq8 : y - 2 = 3 := by
    nlinarith [eq5, eq7]
  linarith [eq8]