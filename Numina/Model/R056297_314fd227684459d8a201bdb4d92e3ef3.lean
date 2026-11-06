import Mathlib

theorem algebra_183457 {a r : ℚ} (hr : r ≠ 0) (h : a / (1 - r) = 10) (h' : (a + 4) / (1 - r) = 15) :
    r = 1 / 5 := by
  have h1 : 1 - r ≠ 0 := by
    by_contra h2
    have h3 : a / (1 - r) = 0 := by
      rw [h2]
      norm_num
      all_goals
        nlinarith
    linarith

  have eq1 : a = 10 * (1 - r) := by 
    have h2 : 1 - r ≠ 0 := h1 
    field_simp [h2] at h 
    linarith

  have eq2 : a + 4 = 15 * (1 - r) := by 
    have h2 : 1 - r ≠ 0 := h1 
    field_simp [h2] at h' 
    linarith

  rw [eq1] at eq2

  linarith