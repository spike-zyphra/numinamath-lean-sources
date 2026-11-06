import Mathlib

open Real

theorem algebra_224495 : sin (37 * π / 180) * (cos (34 * π / 180))^2 +
    2 * sin (34 * π / 180) * cos (37 * π / 180) * cos (34 * π / 180) -
    sin (37 * π / 180) * (sin (34 * π / 180))^2 = (Real.sqrt 6 + Real.sqrt 2) / 4 := by

  have h1 : sin (37 * π / 180) * (cos (34 * π / 180))^2 + 2 * sin (34 * π / 180) * cos (37 * π / 180) * cos (34 * π / 180) - sin (37 * π / 180) * (sin (34 * π / 180))^2 =
    sin (37 * π / 180) * cos (2 * (34 * π / 180)) + sin (2 * (34 * π / 180)) * cos (37 * π / 180) := by
    have hcos2 : cos (2 * (34 * π / 180)) = 2 * (cos (34 * π / 180))^2 - 1 := by
      rw [cos_two_mul]
    have hsin2 : sin (2 * (34 * π / 180)) = 2 * sin (34 * π / 180) * cos (34 * π / 180) := by
      rw [sin_two_mul]
    rw [hsin2, hcos2]
    ring_nf
    <;> simp [sin_sq]
    <;> ring_nf <;> simp [cos_two_mul]
    <;> ring_nf
  rw [h1]
  have h2 : sin (37 * π / 180) * cos (2 * (34 * π / 180)) + sin (2 * (34 * π / 180)) * cos (37 * π / 180) =
    sin ((37 * π / 180) + (2 * (34 * π / 180))) := by
    rw [sin_add]
    <;> ring_nf
    <;> simp [sin_add, cos_add]
    <;> ring_nf
  rw [h2]
  have h3 : (37 * π / 180 : ℝ) + (2 * (34 * π / 180)) = (105 * π / 180 : ℝ) := by
    linarith
  rw [h3]
  have h4 : 105 * π / 180 = Real.pi / 3 + Real.pi / 4 := by
    linarith [Real.pi_pos]
  rw [h4]
  have h5 : sin (Real.pi / 3 + Real.pi / 4) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
    rw [sin_add]
    have h5 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    have h6 : cos (Real.pi / 3) = 1 / 2 := by
      exact cos_pi_div_three
    have h7 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact sin_pi_div_four
    have h8 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    rw [h5, h6, h7, h8]
    have h9 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
      calc
        Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * 2) := by
          rw [Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt 6 := by
          norm_num
    field_simp [h9]
    <;> ring_nf
    <;> norm_num
    <;> ring_nf <;> norm_num
  linarith [h5]