import Mathlib

open Real

theorem algebra_10437 : 1 / sin (π / 18) - sqrt 3 / cos (π / 18) = 4 := by
  have h1 : sin (π / 18) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : cos (π / 18) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have eq1 : 1 / sin (π / 18) - sqrt 3 / cos (π / 18) = (cos (π / 18) - sqrt 3 * sin (π / 18)) / (sin (π / 18) * cos (π / 18)) := by
    field_simp [h1, h2]
    <;> ring
  rw [eq1]
  have eq2 : cos (π / 18) - sqrt 3 * sin (π / 18) = 4 * sin (π / 18) * cos (π / 18) := by
    have h3 : cos (π / 18) - sqrt 3 * sin (π / 18) = 2 * sin (2 * (π / 18)) := by
      have h4 : sin (2 * (π / 18)) = 2 * sin (π / 18) * cos (π / 18) := by
        rw [sin_two_mul]
      have h7 : sin (2 * (π / 18)) = sin (π / 6 - (π / 18)) := by
        ring_nf
      rw [h7]
      rw [sin_sub]
      have h5 : sin (π / 6) = 1 / 2 := by
        rw [sin_pi_div_six]
      have h6 : cos (π / 6) = Real.sqrt 3 / 2 := by
        rw [cos_pi_div_six]
      rw [h5, h6]
      all_goals nlinarith
    have h4 : 4 * sin (π / 18) * cos (π / 18) = 2 * sin (2 * (π / 18)) := by
      have h5 : sin (2 * (π / 18)) = 2 * sin (π / 18) * cos (π / 18) := by
        rw [sin_two_mul]
      nlinarith [h5]
    linarith [h3, h4]
  have eq3 : (cos (π / 18) - sqrt 3 * sin (π / 18)) / (sin (π / 18) * cos (π / 18)) = 4 := by
    rw [eq2]
    have h5 : sin (π / 18) * cos (π / 18) > 0 := by
      nlinarith [h1, h2]
    have h7 : sin (π / 18) * cos (π / 18) ≠ 0 := by
      nlinarith [h1, h2]
    field_simp [h7]
    <;> nlinarith [h1, h2]
  exact eq3