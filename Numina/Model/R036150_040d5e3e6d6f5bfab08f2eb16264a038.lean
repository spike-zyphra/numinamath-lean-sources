import Mathlib

open Real Set
open scoped Real

theorem calculus_23057 : 8 * (cos (π / 18))^2 - 1 / sin (π / 18) = 2 := by
  have h1 : sin (π / 18) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have eq1 : sin (π / 18) ≠ 0 := by linarith [h1]
  have eq2 : 8 * (cos (π / 18))^2 - 1 / sin (π / 18) = 2 := by 
    field_simp [eq1]
    have h2 : 8 * (cos (π / 18))^2 * sin (π / 18) - 2 * sin (π / 18) - 1 = 0 := by
      have h3 : cos (π / 18)^2 = 1 - sin (π / 18) ^ 2 := by 
        rw [←Real.cos_sq_add_sin_sq (π / 18)]
        linarith
      rw [h3] at *
      have h5 : 8 * (1 - sin (π / 18) ^ 2) * sin (π / 18) - 2 * sin (π / 18) - 1 = 0 := by
        have h5 : 8 * (sin (π / 18)) ^ 3 - 6 * (sin (π / 18)) + 1 = 0 := by
          have h8 : sin (3 * (π / 18)) = 3 * sin (π / 18) - 4 * (sin (π / 18) ) ^ 3 := by 
            rw [sin_three_mul]
          have h9 : 3 * (π / 18) = (π / 6) := by 
            ring_nf
          rw [h9] at h8
          have h10 : sin (π / 6) = 1 / 2 := by 
            rw [sin_pi_div_six]
          rw [h10] at h8
          nlinarith 
        nlinarith 
      linarith 
    nlinarith 
  exact eq2