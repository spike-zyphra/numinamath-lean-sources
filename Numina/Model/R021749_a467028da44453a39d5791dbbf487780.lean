import Mathlib

theorem algebra_10224 {x y : ℤ} (h₀ : x + y = 45) (h₁ : x - y = 3) :
    min x y = 21 := by 
  have h2 : x = 24 := by 
    have eq1 : x + y = 45 := h₀
    have eq2 : x - y = 3 := h₁
    have eq3 : x = 24 := by 
      omega
    exact eq3
  have h3 : y = 21 := by 
    rw [h2] at h₀
    omega
  rw [h2, h3]
  all_goals norm_num