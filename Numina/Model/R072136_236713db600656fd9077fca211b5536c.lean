import Mathlib

theorem algebra_290925 {x y : ℚ} (h₀ : y - 1 ≠ 0) (h₁ : x / (y - 1) = 1 / 3)
    (h₂ : (x + 4) / y = 1 / 2) : x / y = 7 / 22 := by
  have h3 : y ≠ 0 := by
    by_contra h3
    rw [h3] at h₂
    norm_num at h₂
    all_goals try linarith
  
  have eq1 : 3 * x = y - 1 := by
    have h₃ : y - 1 ≠ 0 := h₀
    field_simp [h₃] at h₁
    linarith
  
  have eq2 : 2 * (x + 4) = y := by
    have h₄ : y ≠ 0 := h3
    field_simp [h₄] at h₂
    linarith
  
  have h₅ : x = 7 := by
    linarith
  
  have h₆ : y = 22 := by
    rw [h₅] at eq2
    nlinarith
  
  have h₇ : x / y = 7 / 22 := by 
    rw [h₅, h₆]
  
  exact h₇