import Mathlib

open Real

theorem algebra_288849 (α β γ : ℝ) (h : α + β + γ = π) :
    cos α + cos β + cos γ = 4 * sin (α / 2) * sin (β / 2) * sin (γ / 2) + 1 ∧
    cos α + cos β - cos γ = 4 * cos (α / 2) * cos (β / 2) * sin (γ / 2) - 1 := by
  have h1 : γ = π - (α + β) := by linarith
  constructor
  · -- Proof of the first identity
    rw [h1]
    have h2 : cos α + cos β + cos (π - (α + β)) = 1 + 4 * sin (α / 2) * sin (β / 2) * sin ((π - (α + β)) / 2) := by
      have h3 : cos (π - (α + β)) = -cos (α + β) := by
        rw [cos_pi_sub]
      rw [h3]
      have h4 : cos (α + β) = cos α * cos β - sin α * sin β := by
        rw [cos_add]
      rw [h4]
      have h5 : sin ((π - (α + β)) / 2) = cos ((α + β) / 2) := by
        have h6 : (π - (α + β)) / 2 = π / 2 - ( (α + β) / 2 ) := by ring
        rw [h6]
        have h7 : sin (π / 2 - ((α + β) / 2)) = cos ((α + β) / 2) := by
          rw [sin_pi_div_two_sub]
        linarith
      rw [h5]
      have h8 : sin α = 2 * sin (α / 2) * cos (α / 2) := by
        rw [←sin_two_mul]
        ring_nf
      have h9 : cos α = 1 - 2 * (sin (α / 2) ) ^ 2 := by
        have h14 : sin (α / 2) ^ 2 = (1 - cos α) / 2 := by
          rw [sin_sq_eq_half_sub]
          ring_nf
        nlinarith
      have h8' : sin β = 2 * sin (β / 2) * cos (β / 2) := by
        rw [←sin_two_mul]
        ring_nf
      have h9' : cos β = 1 - 2 * (sin (β / 2) ) ^ 2 := by
        have h14 : sin (β / 2) ^ 2 = (1 - cos β) / 2 := by
          rw [sin_sq_eq_half_sub]
          ring_nf
        nlinarith
      have h10 : cos ((α + β) / 2) = cos (α / 2) * cos (β / 2) - sin (α / 2) * sin (β / 2) := by
        rw [show (α + β) / 2 = α / 2 + β / 2 by ring]
        rw [cos_add]
      rw [h8, h9, h8', h9', h10]
      nlinarith [sin_sq_add_cos_sq (α / 2), sin_sq_add_cos_sq (β / 2), sq_nonneg (sin (α / 2) - sin (β / 2) ), sq_nonneg (cos (α / 2) - cos (β / 2) ), sq_nonneg (sin (α / 2) - cos (β / 2) ), sq_nonneg (sin (β / 2) - cos (α / 2) ), sin_sq_add_cos_sq (α / 2), sin_sq_add_cos_sq (β / 2) ]
    linarith
  · -- Proof of the second identity
    rw [h1]
    have h2 : cos α + cos β - cos (π - (α + β)) = -1 + 4 * cos (α / 2) * cos (β / 2) * sin ((π - (α + β)) / 2) := by
      have h3 : cos (π - (α + β)) = -cos (α + β) := by
        rw [cos_pi_sub]
      rw [h3]
      have h4 : cos (α + β) = cos α * cos β - sin α * sin β := by
        rw [cos_add]
      rw [h4]
      have h5 : sin ((π - (α + β)) / 2) = cos ((α + β) / 2) := by
        have h6 : (π - (α + β)) / 2 = π / 2 - ( (α + β) / 2 ) := by ring
        rw [h6]
        have h7 : sin (π / 2 - ((α + β) / 2)) = cos ((α + β) / 2) := by
          rw [sin_pi_div_two_sub]
        linarith
      rw [h5]
      have h8 : sin α = 2 * sin (α / 2) * cos (α / 2) := by
        rw [←sin_two_mul]
        ring_nf
      have h9 : cos α = 1 - 2 * (sin (α / 2) ) ^ 2 := by
        have h14 : sin (α / 2) ^ 2 = (1 - cos α) / 2 := by
          rw [sin_sq_eq_half_sub]
          ring_nf
        nlinarith
      have h8' : sin β = 2 * sin (β / 2) * cos (β / 2) := by
        rw [←sin_two_mul]
        ring_nf
      have h9' : cos β = 1 - 2 * (sin (β / 2) ) ^ 2 := by
        have h14 : sin (β / 2) ^ 2 = (1 - cos β) / 2 := by
          rw [sin_sq_eq_half_sub]
          ring_nf
        nlinarith
      have h10 : cos ((α + β) / 2) = cos (α / 2) * cos (β / 2) - sin (α / 2) * sin (β / 2) := by
        rw [show (α + β) / 2 = α / 2 + β / 2 by ring]
        rw [cos_add]
      rw [h8, h9, h8', h9', h10]
      nlinarith [sin_sq_add_cos_sq (α / 2), sin_sq_add_cos_sq (β / 2), sq_nonneg (sin (α / 2) - sin (β / 2) ), sq_nonneg (cos (α / 2) - cos (β / 2) ), sq_nonneg (sin (α / 2) - cos (β / 2) ), sq_nonneg (sin (β / 2) - cos (α / 2) ), sin_sq_add_cos_sq (α / 2), sin_sq_add_cos_sq (β / 2) ]
    linarith