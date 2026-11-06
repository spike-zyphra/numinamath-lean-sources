import Mathlib

open Real Set
open scoped Real

theorem algebra_185903 (α : Real) :
  sin (4 * α) - 2 * (cos (2 * α))^2 + 1 = sqrt 2 * sin (4 * α - π / 4) := by
  have h1 : cos (4 * α) = 2 * (cos (2 * α)) ^ 2 - 1 := by 
    have h2 : cos (4 * α) = cos (2 * (2 * α)) := by ring_nf
    rw [h2]
    rw [cos_two_mul]
  have h2 : sin (4 * α) - 2 * (cos (2 * α)) ^ 2 + 1 = sin (4 * α) - cos (4 * α) := by
    rw [h1]
    all_goals ring
  rw [h2]
  have h3 : sqrt 2 * sin (4 * α - π / 4) = sin (4 * α) - cos (4 * α) := by
    have h4 : sin (4 * α - π / 4) = sin (4 * α) * cos (π / 4) - cos (4 * α) * sin (π / 4) := by 
      rw [sin_sub]
    have h5 : sin (π / 4) = sqrt 2 / 2 := by 
      have h5 : sin (π / 4) = sqrt 2 / 2 := by 
        exact sin_pi_div_four
      linarith
    have h6 : cos (π / 4) = sqrt 2 / 2 := by 
      have h6 : cos (π / 4) = sqrt 2 / 2 := by 
        exact cos_pi_div_four
      linarith
    rw [h4]
    rw [h5, h6]
    have eq1 : sqrt 2 * (sin (4 * α) * (sqrt 2 / 2) - cos (4 * α) * (sqrt 2 / 2)) =
        sin (4 * α) - cos (4 * α) := by
      have eq8 : sqrt 2 * (sin (4 * α) * (sqrt 2 / 2) - cos (4 * α) * (sqrt 2 / 2)) =
          sqrt 2 * (sin (4 * α) * (sqrt 2 / 2)) - sqrt 2 * (cos (4 * α) * (sqrt 2 / 2)) := by ring
      rw [eq8]
      have eq3 : sqrt 2 * (sin (4 * α) * (sqrt 2 / 2)) = sin (4 * α) := by
        calc
          sqrt 2 * (sin (4 * α) * (sqrt 2 / 2)) = sqrt 2 * sqrt 2 / 2 * sin (4 * α) := by 
            ring_nf
          _ = (2 / 2) * sin (4 * α) := by 
            have h11 : sqrt 2 * sqrt 2 = 2 := by
              exact Real.mul_self_sqrt (by linarith)
            rw [h11]
          _ = 1 * sin (4 * α) := by 
            ring_nf
          _ = sin (4 * α) := by 
            ring
      have eq4 : sqrt 2 * (cos (4 * α) * (sqrt 2 / 2)) = cos (4 * α) := by
        calc 
          sqrt 2 * (cos (4 * α) * (sqrt 2 / 2)) = sqrt 2 * sqrt 2 / 2 * cos (4 * α) := by 
            ring_nf
          _ = (2 / 2) * cos (4 * α) := by 
            have h11 : sqrt 2 * sqrt 2 = 2 := by
              exact Real.mul_self_sqrt (by linarith)
            rw [h11]
          _ = 1 * cos (4 * α) := by 
            ring_nf
          _ = cos (4 * α) := by 
            ring
      rw [eq3, eq4]
      <;> ring
    linarith [eq1]
  linarith [h3]