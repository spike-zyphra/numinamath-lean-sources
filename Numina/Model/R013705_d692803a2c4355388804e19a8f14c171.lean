import Mathlib

open Real Set
open scoped Real

theorem algebra_162741 (α : ℝ) :
  (cos (2 * α))^4 - 6 * (cos (2 * α))^2 * (sin (2 * α))^2 +
  (sin (2 * α))^4 = cos (8 * α) := by
  have h1 : (cos (2 * α))^4 - 6 * (cos (2 * α))^2 * (sin (2 * α))^2 + (sin (2 * α))^4 = 1 - 8 * (cos (2 * α))^2 * (sin (2 * α))^2 := by
    have h2 : (cos (2 * α))^4 + (sin (2 * α))^4 = ((cos (2 * α))^2 + (sin (2 * α))^2)^2 - 2 * (cos (2 * α))^2 * (sin (2 * α))^2 := by
      ring
    have h3 : (cos (2 * α))^2 + (sin (2 * α))^2 = 1 := by
      exact Real.cos_sq_add_sin_sq (2 * α)
    calc
      (cos (2 * α))^4 - 6 * (cos (2 * α))^2 * (sin (2 * α))^2 + (sin (2 * α))^4
        = ((cos (2 * α))^4 + (sin (2 * α))^4) - 6 * (cos (2 * α))^2 * (sin (2 * α))^2 := by ring
      _ = (((cos (2 * α))^2 + (sin (2 * α))^2)^2 - 2 * (cos (2 * α))^2 * (sin (2 * α))^2) - 6 * (cos (2 * α))^2 * (sin (2 * α))^2 := by
        rw [h2]
      _ = (1^2 - 2 * (cos (2 * α))^2 * (sin (2 * α))^2) - 6 * (cos (2 * α))^2 * (sin (2 * α))^2 := by
        rw [h3]
      _ = 1 - 8 * (cos (2 * α))^2 * (sin (2 * α))^2 := by
        ring
  rw [h1]
  have h2 : 1 - 8 * (cos (2 * α))^2 * (sin (2 * α))^2 = 1 - 2 * (sin (4 * α))^2 := by
    have h3 : sin (4 * α) = 2 * sin (2 * α) * cos (2 * α) := by
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [sin_two_mul]
    calc
      1 - 8 * (cos (2 * α))^2 * (sin (2 * α))^2
          = 1 - 2 * (2 * sin (2 * α) * cos (2 * α))^2 := by
            ring_nf
      _ = 1 - 2 * (sin (4 * α))^2 := by
        rw [h3]
  have h3 : 1 - 2 * (sin (4 * α))^2 = cos (8 * α) := by
    have h4 : cos (8 * α) = 1 - 2 * (sin (4 * α))^2 := by
      have h5 : 8 * α = 2 * (4 * α) := by ring
      rw [h5]
      rw [cos_two_mul]
      rw [sin_sq]
      <;> ring
    linarith [h4]
  rw [h2, h3]