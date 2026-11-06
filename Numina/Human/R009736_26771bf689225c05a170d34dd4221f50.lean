import Mathlib
/-Two cars are driving directly towards each other such that one is twice as fast as the other. The distance between their starting points is 4 miles. When the two cars meet, how many miles is the faster car from its starting point?-/
theorem algebra_609202 :
  -- Assumptions: Two cars travel toward each other, one car's speed is twice the other's, initial distance is 4 miles
  ∀ (v₁ v₂ : ℝ) (t : ℝ),
    v₁ > 0 → v₂ > 0 →
    v₁ = 2 * v₂ →      -- One car's speed is twice the other's
    v₁ * t + v₂ * t = 4 →  -- When they meet, total distance traveled equals initial distance 4
    v₁ * t = 8/3 :=   by -- To prove: The faster car travels 8/3 miles
  intros v₁ v₂ t hv₁ hv₂ hspeed hmeeting

  -- Substitute v₁ = 2*v₂ into the meeting equation
  rw [hspeed] at hmeeting

  -- Rewrite as 3*v₂*t = 4
  have h1 : 2 * v₂ * t + v₂ * t = 3 * v₂ * t := by ring
  rw [h1] at hmeeting

  -- Solve for v₂*t
  have h2 : v₂ * t = 4/3 := by
    -- Divide hmeeting by 3
    rw [hmeeting] at h1
    -- Divide by 3
    linarith

  -- Calculate v₁*t
  calc v₁ * t = 2 * v₂ * t := by rw [hspeed]
          _ = 2 * (4/3)  := by linarith
          _ = 8/3        := by norm_num