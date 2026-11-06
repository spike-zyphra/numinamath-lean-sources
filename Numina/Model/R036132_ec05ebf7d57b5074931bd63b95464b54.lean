import Mathlib

open Real Set
open scoped Real

theorem algebra_261473 (α β : ℝ) (h₁ : 2 * (cos α)^3 - sin α * sin (2 * α) ≠ 0) (h₂ : cos β ≠ 0) (h₃ : cos (3 * α) - 4 * (cos α)^3 ≠ 0) :
  (cos (3 * α) + cos α) / (2 * (cos α)^3 - sin α * sin (2 * α)) = 1 ∧ 
  (sin α * sin (α + β) + cos α * cos (α + β)) / cos β = 1 ∧ 
  (sin (3 * α) + 4 * (sin α)^3) / (cos (3 * α) - 4 * (cos α)^3) + tan α = 0 := by

  have h1 : (cos (3 * α) + cos α) / (2 * (cos α)^3 - sin α * sin (2 * α)) = 1 := by
    have h4 : cos (3 * α) = 4 * (cos α)^3 - 3 * cos α := by 
      rw [cos_three_mul]

    have h5 : sin (2 * α) = 2 * sin α * cos α := by 
      rw [sin_two_mul]

    have eq1 : 2 * (cos α)^3 - sin α * sin (2 * α) = 4 * (cos α) ^ 3 - 2 * cos α := by
      rw [h5]
      have h9 : sin α ^ 2 = 1 - cos α ^ 2 := by
        have h10 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
        linarith
      calc
        2 * (cos α) ^ 3 - sin α * (2 * sin α * cos α) = 2 * (cos α) ^ 3 - 2 * sin α ^ 2 * cos α := by ring
        _ = 2 * (cos α) ^ 3 - 2 * (1 - cos α ^ 2) * cos α := by 
          rw [show sin α ^ 2 = 1 - cos α ^ 2 by linarith [h9]]
        _ = 2 * (cos α) ^ 3 - 2 * cos α + 2 * (cos α) ^ 3 := by 
          ring
        _ = 4 * (cos α) ^ 3 - 2 * cos α := by 
          ring

    have eq2 : cos (3 * α) + cos α = 4 * (cos α) ^ 3 - 2 * cos α := by
      rw [h4]
      ring_nf

    rw [eq1, eq2]
    have h400 : (4 * (cos α) ^ 3 - 2 * cos α) / (4 * (cos α) ^ 3 - 2 * cos α) = 1 := by 
      field_simp [(show 4 * (cos α) ^ 3 - 2 * cos α ≠ 0 by 
        by_contra h
        have h40 : 2 * (cos α)^3 - sin α * sin (2 * α) = 0 := by
          rw [eq1] at *
          linarith
        contradiction
      )]
    exact h400
  
  have h2 : (sin α * sin (α + β) + cos α * cos (α + β)) / cos β = 1 := by 
    have hcos : sin α * sin (α + β) + cos α * cos (α + β) = cos β := by 
      have hcos1 : sin α * sin (α + β) + cos α * cos (α + β) = cos ( (α + β) - α ) := by 
        rw [cos_sub]
        ring

      have hcos2 : ( (α + β) - α ) = β := by 
        ring

      rw [hcos2] at hcos1
      linarith

    rw [hcos]
    field_simp [h₂]

  have h3 : (sin (3 * α) + 4 * (sin α)^3) / (cos (3 * α) - 4 * (cos α)^3) + tan α = 0 := by

    have h10 : sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 := by 
      rw [sin_three_mul]

    have h11 : cos (3 * α) = 4 * cos α ^ 3 - 3 * cos α := by 
      rw [cos_three_mul]

    have eq1 : sin (3 * α) + 4 * (sin α) ^ 3 = 3 * sin α := by
      rw [h10]
      ring_nf

    have eq2 : cos (3 * α) - 4 * (cos α)^3 = -3 * cos α := by 
      rw [h11]
      ring_nf

    rw [eq1, eq2]

    have htan : tan α = sin α / cos α := by 
      rw [tan_eq_sin_div_cos]

    have hcosNe0 : cos α ≠ 0 := by 
      by_contra hcos0
      have h400 : cos (3 * α) - 4 * (cos α)^3 = 0 := by
        rw [h11]
        rw [hcos0]
        norm_num

      contradiction

    rw [htan]
    field_simp [hcosNe0]
    <;> ring_nf

  exact ⟨h1, h2, h3⟩