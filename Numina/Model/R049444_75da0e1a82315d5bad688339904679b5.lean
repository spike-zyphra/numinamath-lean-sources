import Mathlib

theorem algebra_15587 (jim bob : ℤ) (h₀ : jim + bob = 180) (h₁ : bob - jim = bob / 2) :
    bob = 120 := by
  have h2 : bob % 2 = 0 := by
    omega
  have h3 : 2 * (bob - jim) = bob := by
    omega
  have h4 : bob = 2 * jim := by 
    linarith 
    all_goals omega
  have hj : jim = 60 := by 
    linarith [h₀, h4]
  linarith [h4, hj]