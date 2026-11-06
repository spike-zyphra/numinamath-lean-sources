import Mathlib

theorem algebra_284469 (p h : ℝ) (h₀ : p / h = 4 / 5) (h₁ : (p - 200) / (h + 100) = 5 / 8) :
    p = 1200 := by

  have h2 : h ≠ 0 := by
    by_contra h3
    rw [h3] at h₀
    norm_num at h₀

  have h3 : h + 100 ≠ 0 := by
    by_contra h4
    rw [h4] at h₁
    norm_num at h₁
  
  have eq1 : 5 * p = 4 * h := by
    have : h ≠ 0 := h2
    field_simp at h₀
    linarith
  
  have eq2 : 8 * (p - 200) = 5 * (h + 100) := by
    have : h + 100 ≠ 0 := h3
    field_simp at h₁
    linarith

  have eq3 : p = 4 / 5 * h := by
    linarith
  
  rw [eq3] at eq2
  
  have eq4 : h = 1500 := by
    linarith
  
  rw [eq4] at eq3
  
  linarith