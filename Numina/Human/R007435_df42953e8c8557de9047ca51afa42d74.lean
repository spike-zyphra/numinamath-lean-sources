import Mathlib

/- 25 students average 84 on a test. Another group of 20 students averages 66. Find the overall average. -/
theorem algebra_18791 (count₁ score₁ count₂ score₂ : ℕ)
    (hc₁ : count₁ = 25) (hc₂ : count₂ = 20)
    (hs₁ : score₁ = 84) (hs₂ : score₂ = 66):
    (score₁ * count₁ + score₂ * count₂) / (count₁ + count₂) = (76 : ℝ) := by 
  subst_vars
  norm_num