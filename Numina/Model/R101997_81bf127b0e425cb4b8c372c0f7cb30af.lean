import Mathlib

theorem algebra_225012 {x y : ℕ} (h₀ : x + y = 363) (h₁ : x / y = 16 ∧ x % y = 6) :
    max x y = 342 := by
  have h2 : x / y = 16 := h₁.1
  have h3 : x % y = 6 := h₁.2
  
  have h4 : x = y * 16 + 6 := by
    rw [←Nat.div_add_mod x y, h2, h3]
    all_goals omega
  
  have h5 : x + y = 363 := h₀
  rw [h4] at h5
  
  have hy : y = 21 := by
    omega
  
  have hx : x = 342 := by
    rw [hy] at h4
    omega
  
  rw [hx, hy]
  norm_num