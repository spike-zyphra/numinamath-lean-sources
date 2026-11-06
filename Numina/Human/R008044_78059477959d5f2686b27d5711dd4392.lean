import Mathlib
open Real
/-
tan (π / 9) * tan (2 * (π / 9)) * tan (4 * (π / 9)) =
-/
theorem algebra_285866 : tan (π / 9) * tan (2 * (π / 9)) * tan (4 * (π / 9)) = √3 := by
  generalize hθ : π / 9 = θ
  calc tan θ * tan (2 * θ) * tan (4 * θ)
    -- Rewrite tan into sin/cos
    _ = ((2 * sin θ * sin (2 * θ)) * sin (4 * θ)) /
        ((2 * cos θ * cos (2 * θ)) * cos (4 * θ)) := by
      simp [tan_eq_sin_div_cos]
      -- Multiply by 2 in both parts of the fraction
      have : 2 * sin θ ≠ 0 := by
        -- Show this to allow us to divide by sin θ
        have : 0 < sin θ := by
          simp_all [<- hθ]
          apply sin_pos_of_pos_of_lt_pi (by positivity)
          have π_lt_mul : π < π * 9 := by field_simp
          linarith
        field_simp
      ring_nf
    -- Apply product to sum formulas to both parts of the fraction
    -- and the symmetric property of cos to simplify cos -θ
    _ = (cos (θ) * sin (4 * θ) - cos (3 * θ) * sin (4 * θ)) /
        (cos (3 * θ) * cos (4 * θ) + cos θ * cos (4 * θ)) := by
      rw [two_mul_sin_mul_sin, two_mul_cos_mul_cos]
      simp [two_mul] -- simplify cos(θ - 2θ) = cos(θ)
      ring_nf
    -- Use cos (π / 3) = 1/2
    _ = (2 * sin (4 * θ) * cos θ - sin (4 * θ)) /
        (2 * cos (4 * θ) * cos θ + cos (4 * θ)) := by
      have : cos (3 * θ) = 1 / 2 := by
        rw [<- hθ]
        convert_to cos (π / 3) = 1 / 2; ring_nf
        exact cos_pi_div_three
      rw [this, add_comm]
      field_simp [mul_comm, <- mul_assoc]
    -- Apply product to sum formula
    _ = (sin (5 * θ) - sin (4 * θ) + sin (3 * θ)) /
        (cos (5 * θ) + cos (4 * θ) + cos (3 * θ)) := by
      rw [two_mul_sin_mul_cos, two_mul_cos_mul_cos]
      ring_nf
    -- Use sin(π / 3) = √3/2
    _ = (sin (5 * θ) - sin (4 * θ) + √3 / 2) /
        (cos (5 * θ) + cos (4 * θ) + 1 / 2) := by
      simp [show 3 * θ = π / 3 by rw [<- hθ]; ring_nf]
    -- Use sum/sub to product identities
    _ = (2 * sin (θ / 2) * cos (9 * θ / 2) + √3/2) /
        (2 * cos (9 * θ / 2) * cos (θ / 2) + 1/2) := by
      rw [sin_sub_sin, cos_add_cos]
      ring_nf
    -- Use cos(π/2) = 0 to cancel terms
    _ = √3 := by
      field_simp [show 9 * θ / 2 = π / 2 by rw [<- hθ]; ring_nf]