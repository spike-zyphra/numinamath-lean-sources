import Mathlib

open Real

theorem algebra_163960 : (cos (64 * π / 180) * cos (4 * π / 180) -
    cos (86 * π / 180) * cos (26 * π / 180)) /
    (cos (71 * π / 180) * cos (41 * π / 180) -
    cos (49 * π / 180) * cos (19 * π / 180)) = -1 := by
  have h1 : cos (86 * π / 180) = sin (4 * π / 180) := by
    have h2 : 86 * π / 180 = Real.pi / 2 - 4 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [cos_pi_div_two_sub]
  have h2 : cos (26 * π / 180) = sin (64 * π / 180) := by
    have h3 : 26 * π / 180 = Real.pi / 2 - 64 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h3]
    rw [cos_pi_div_two_sub]
  have h3 : cos (64 * π / 180) * cos (4 * π / 180) - cos (86 * π / 180) * cos (26 * π / 180) = cos (68 * π / 180) := by
    rw [h1, h2]
    have h4 : cos (64 * π / 180) * cos (4 * π / 180) - sin (4 * π / 180) * sin (64 * π / 180) = cos (64 * π / 180 + 4 * π / 180) := by
      rw [cos_add]
      <;> ring
    have h5 : 64 * π / 180 + 4 * π / 180 = 68 * π / 180 := by
      linarith
    rw [h4, h5]
  have h4 : cos (71 * π / 180) = sin (19 * π / 180) := by
    have h5 : 71 * π / 180 = Real.pi / 2 - 19 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h5]
    rw [cos_pi_div_two_sub]
  have h5 : cos (41 * π / 180) = sin (49 * π / 180) := by
    have h6 : 41 * π / 180 = Real.pi / 2 - 49 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h6]
    rw [cos_pi_div_two_sub]
  have h6 : cos (71 * π / 180) * cos (41 * π / 180) - cos (49 * π / 180) * cos (19 * π / 180) = - cos (68 * π / 180) := by
    rw [h4, h5]
    have h7 : sin (19 * π / 180) * sin (49 * π / 180) - cos (49 * π / 180) * cos (19 * π / 180) = - cos (49 * π / 180 + 19 * π / 180) := by
      rw [cos_add]
      ring
    have h8 : 49 * π / 180 + 19 * π / 180 = 68 * π / 180 := by
      linarith
    rw [h7, h8]
  have h7 : cos (68 * π / 180) ≠ 0 := by
    have h10 : 0 < 68 * π / 180 := by
      linarith [Real.pi_pos]
    have h11 : 68 * π / 180 < Real.pi := by
      linarith [Real.pi_pos]
    have h12 : cos (68 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    linarith
  rw [h3, h6]
  field_simp [h7]
  <;> ring