import Mathlib

theorem algebra_18958 {x y : ℝ} (hx : x < y) (h₀ : x / y = 3 / 5) (h₁ : (x - 4) / (y + 8) = 2 / 7) :
    y = 20 := by
  have h2 : y ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num at h₀
    all_goals linarith
  have h3 : y + 8 ≠ 0 := by
    by_contra h
    have h4 : y = -8 := by linarith
    rw [h4] at h₁
    norm_num at h₁
    all_goals linarith
  have eq1 : 5 * x = 3 * y := by
    have h2' : y ≠ 0 := h2
    field_simp [h2'] at h₀
    linarith
  have eq2 : 7 * (x - 4) = 2 * (y + 8) := by
    have h3' : y + 8 ≠ 0 := h3
    field_simp [h3'] at h₁
    linarith
  have eq3 : x = 3 / 5 * y := by
    linarith [eq1]
  rw [eq3] at eq2
  linarith