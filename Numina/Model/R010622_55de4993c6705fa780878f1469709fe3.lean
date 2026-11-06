import Mathlib

theorem algebra_158081 (v₁ v₂ t: ℝ) (hv : 0 < v₁)
    (h₀ : (6 + 12) * v₂ = 12 * v₁) 
    (h₁ : (6 + t) * v₂ = t * 2 * v₁) :
    t = 3 := by
  -- From the first equation, (6 + 12) * v₂ = 12 * v₁
  -- Simplify to get v₂ = (2/3) * v₁
  have h2 : v₂ = (2 / 3) * v₁ := by 
    linarith
  rw [h2] at h₁
  -- Now the equation becomes (6 + t) * (2/3) * v₁ = 2 * t * v₁
  -- Rearrange this to standard form
  have h3 : (6 + t) * (2 / 3) * v₁ - 2 * t * v₁ = 0 := by linarith
  -- Factor out v₁ from the left side
  have h4 : v₁ * ( ((6 + t) * (2 / 3) ) - 2 * t ) = 0 := by
    linarith
  -- Since v₁ > 0 (hv: 0 < v₁), coefficient must be zero
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where v₁ = 0, but we have h₁: 0 < v₁, so contradiction
    linarith
  · -- Case where coefficient is zero
    linarith