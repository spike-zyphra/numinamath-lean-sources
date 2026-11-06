import Mathlib

open Real Set

theorem inequalities_150220 (a b : ℝ) (θ : ℝ) :
    (cos (θ + a) + b * cos θ) ^ 2 ≤ 1 + 2 * b * cos a + b ^ 2 := by 
  have h1 : cos (θ + a) = cos θ * cos a - sin θ * sin a := by 
    rw [cos_add]
  rw [h1]
  have h2 : (cos θ * cos a - sin θ * sin a + b * cos θ) ^ 2 ≤ 1 + 2 * b * cos a + b ^ 2 := by 
    nlinarith [sq_nonneg (cos θ * (cos a + b) - sin θ * sin a), 
          sq_nonneg (sin θ * (cos a + b) + cos θ * sin a), 
          Real.cos_sq_add_sin_sq θ, 
          Real.cos_sq_add_sin_sq a, 
          sq_nonneg (cos θ * sin a + sin θ * (b + cos a)), 
          sq_nonneg (cos θ * (cos a - b) - sin θ * sin a)
        ]
  linarith