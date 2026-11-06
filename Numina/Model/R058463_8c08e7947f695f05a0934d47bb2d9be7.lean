import Mathlib

open Real

theorem algebra_1664 (θ : Real) : 32 * (cos θ)^6 - cos (6 * θ) - 6 * cos (4 * θ) - 15 * cos (2 * θ) = 10 := by
  have h1 : cos (6 * θ) = 32 * (cos θ)^6 - 48 * (cos θ)^4 + 18 * (cos θ)^2 - 1 := by
    have h1 : cos (6 * θ) = 2 * cos (3 * θ) * cos (3 * θ) - 1 := by
      rw [show 6 * θ = 2 * (3 * θ) by ring]
      rw [cos_two_mul]
      <;> ring_nf <;> simp [mul_assoc]
      <;> ring_nf
    have h2 : cos (3 * θ) = 4 * (cos θ)^3 - 3 * cos θ := by
      rw [cos_three_mul]
    rw [h2] at h1
    nlinarith [sq_nonneg (4 * (cos θ)^3 - 3 * cos θ)]
  
  have h2 : cos (4 * θ) = 2 * (cos (2 * θ))^2 - 1 := by
    rw [show 4 * θ = 2 * (2 * θ) by ring]
    rw [cos_two_mul]
  
  have h3 : cos (2 * θ) = 2 * (cos θ)^2 - 1 := by
    rw [cos_two_mul]

  rw [h1]
  rw [h2]
  rw [h3]
  
  nlinarith [sq_nonneg (cos θ), sq_nonneg (cos θ - 1), sq_nonneg (cos θ + 1)]