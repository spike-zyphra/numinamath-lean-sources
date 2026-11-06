import Mathlib

theorem negated_calculus_70218 (d : ℝ)
    (h₀ : d > 0)
    (v₁ v₂ v₃ v₄ : ℝ)
    (h₁ : v₁ = 3)
    (h₂ : v₂ = 2)
    (h₃ : v₃ = 6)
    (h₄ : v₄ = 3) :
    (4 * d) / (d / v₁ + d / v₂ + d / v₃ + d / v₄) = 3 := by
  rw [h₁, h₂, h₃, h₄]
  have h5 : d ≠ 0 := by linarith
  -- The average speed is given by the formula: total distance divided by total time.
  -- The total distance is 4d.
  -- The total time is calculated as the sum of the reciprocals of the speeds multiplied by the distance.
  -- Substitute v₁ and v₂ to compute each term.
  field_simp [h5]
  <;> ring_nf <;> field_simp [h5] at *
  <;> ring