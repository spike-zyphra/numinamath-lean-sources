import Mathlib

theorem algebra_185674 (α β : ℝ) :
    (Real.sin (α + 2 * β))^2 + (Real.sin (α - 2 * β))^2 - 1 =
    -Real.cos (2 * α) * Real.cos (4 * β) := by
  have h1 : Real.sin (α + 2 * β) = Real.sin α * Real.cos (2 * β) + Real.cos α * Real.sin (2 * β) := by
    rw [Real.sin_add]
  have h2 : Real.sin (α - 2 * β) = Real.sin α * Real.cos (2 * β) - Real.cos α * Real.sin (2 * β) := by
    rw [Real.sin_sub]
    <;> ring
  rw [h1, h2]
  have h3 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h4 : Real.cos (4 * β) = 2 * Real.cos (2 * β) ^ 2 - 1 := by
    have h4 : Real.cos (4 * β) = Real.cos (2 * (2 * β)) := by ring_nf
    rw [h4]
    rw [Real.cos_two_mul]
  rw [h3, h4]
  have h5 : Real.sin (2 * β) ^ 2 = 1 - Real.cos (2 * β) ^ 2 := by
    have h1 : Real.sin (2 * β) ^ 2 + Real.cos (2 * β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * β)
    linarith
  have h6 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
    have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linarith
  simp [pow_two] at *
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq (2 * β), 
          sq_nonneg (Real.sin α ^ 2 - Real.cos α ^ 2), 
          sq_nonneg (Real.sin (2 * β) ^ 2 - Real.cos (2 * β) ^ 2), 
          sq_nonneg (Real.cos α ^ 2 - Real.cos (2 * β) ^ 2), 
          sq_nonneg (Real.sin α * Real.sin (2 * β)), 
          sq_nonneg (Real.cos α * Real.cos (2 * β)), 
          Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq (2 * β)
        ]