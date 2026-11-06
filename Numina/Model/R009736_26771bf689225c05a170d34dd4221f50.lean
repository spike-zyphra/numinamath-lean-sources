import Mathlib
theorem algebra_609202 :
  -- Assumptions: Two cars travel toward each other, one car's speed is twice the other's, initial distance is 4 miles
  ∀ (v₁ v₂ : ℝ) (t : ℝ),
    v₁ > 0 → v₂ > 0 →
    v₁ = 2 * v₂ →      -- One car's speed is twice the other's
    v₁ * t + v₂ * t = 4 →  -- When they meet, total distance traveled equals initial distance 4
    v₁ * t = 8/3 :=   by
    intro v₁ v₂ t hv₁ hv₂ h₁ h₂
    rw [h₁] at h₂
    have h₁₁ : 2 * v₂ * t + v₂ * t = 4 := by linarith
    have h₂₂ : 3 * (v₂ * t) = 4 := by
      nlinarith
    have h₃₃ : v₂ * t = 4 / 3 := by
      linarith
    have h₁₁₁ : v₁ * t = 2 * (v₂ * t) := by
      rw [h₁]
      ring
    rw [h₁₁₁]
    rw [h₃₃]
    all_goals
      linarith