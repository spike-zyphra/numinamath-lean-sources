import Mathlib

open Real

theorem algebra_327398 : 1 / sin (π / 18) - sqrt 3 / cos (π / 18) = 4 := by
  have h1 : sin (π / 18) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : cos (π / 18) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h3 : cos (7 * π / 18) = sin (π / 9) := by
    have h4 : 7 * π / 18 = π / 2 - π / 9 := by
      linarith [Real.pi_pos]
    rw [h4]
    have h5 : cos (π / 2 - π / 9) = sin (π / 9) := by
      rw [cos_pi_div_two_sub]
    exact h5
  -- We can transform the left-hand side using angle addition.
  -- Note that cos(π/18) - sqrt3 sin(π/18) = 2 cos(π/18 + π/3).
  have h4 : cos (π / 18) - sqrt 3 * sin (π / 18) = 2 * cos (7 * π / 18) := by
    have h5 : cos (π / 18) - sqrt 3 * sin (π / 18) = 2 * cos (π / 18 + π / 3) := by
      rw [cos_add]
      have h7 : cos (π / 3) = 1 / 2 := by
        exact cos_pi_div_three
      have h8 : sin (π / 3) = Real.sqrt 3 / 2 := by
        exact sin_pi_div_three
      rw [h7, h8]
      ring_nf
    have h6 : π / 18 + π / 3 = 7 * π / 18 := by
      linarith [Real.pi_pos]
    rw [h5, h6]
  have h7 : cos (π / 18) - Real.sqrt 3 * sin (π / 18) = 2 * sin (π / 9) := by
    rw [h4]
    rw [h3]
  have h10 : sin (π / 18) * cos (π / 18) = (1 / 2) * sin (π / 9) := by
    have h8' : sin (π / 18) * cos (π / 18) = (1 / 2) * sin (2 * (π / 18)) := by
      rw [sin_two_mul]
      <;> ring_nf
    have h9' : 2 * (π / 18) = π / 9 := by
      ring_nf
    rw [h9'] at h8'
    linarith
  -- Now, the original expression becomes (2 sin(π/9) ) / ( (1/2) sin(π/9) ) = 4.
  have h11 : 1 / sin (π / 18) - sqrt 3 / cos (π / 18) =
      (cos (π / 18) - Real.sqrt 3 * sin (π / 18)) / (sin (π / 18) * cos (π / 18)) := by
    field_simp [show sin (π / 18) ≠ 0 by linarith [h1], 
      show cos (π / 18) ≠ 0 by linarith [h2]]
    <;> ring_nf
  rw [h11]
  rw [show cos (π / 18) - Real.sqrt 3 * sin (π / 18) = 2 * sin (π / 9) by linarith [h7]]
  rw [show sin (π / 18) * cos (π / 18) = (1 / 2) * sin (π / 9) by linarith [h10]]
  have hsin : sin (π / 9) ≠ 0 := by
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  field_simp [hsin]
  <;> ring_nf