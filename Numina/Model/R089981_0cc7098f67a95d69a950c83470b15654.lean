import Mathlib

theorem algebra_265659 (d r : ℕ) (h₀ : d = 252) (h₁ : r = d / 28) (h₂ : r - 10 = 10)
    (h₃ : (r + 10) * (r + 10) = d * (r + 10)) :
    r * (r + 10) = 171 := by

  have hr : r = 20 := by
    omega

  rw [hr] at h₁ 
  rw [h₀] at h₁ 
  all_goals omega