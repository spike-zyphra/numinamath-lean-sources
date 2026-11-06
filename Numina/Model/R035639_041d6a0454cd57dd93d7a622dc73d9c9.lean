import Mathlib

open Real

theorem algebra_6067 : (cos (π / 9)) * (cos (2 * π / 9)) * (cos (4 * π / 9)) = 1 / 8 := by
  have h1 : sin (π / 9) ≠ 0 := by
    have h1 : 0 < π / 9 := by linarith [Real.pi_pos]
    have h2 : 0 < sin (π / 9) := by apply sin_pos_of_pos_of_lt_pi; linarith; linarith [Real.pi_pos]
    linarith
  have h2 : (cos (π / 9)) * (cos (2 * π / 9)) * (cos (4 * π / 9)) =
      ( (1 / 8) * sin (8 * (π / 9)) ) / (sin (π / 9)) := by
    have h4 : sin (8 * (π / 9)) = 8 * sin (π / 9) * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) := by
      have h10 : sin (8 * (π / 9)) = 2 * sin (4 * (π / 9)) * cos (4 * (π / 9)) := by
        rw [show 8 * (π / 9) = 2 * (4 * (π / 9)) by ring]
        rw [sin_two_mul]
        <;> ring_nf
      have h100 : sin (4 * (π / 9)) = 2 * sin (2 * (π / 9)) * cos (2 * (π / 9)) := by
        rw [show 4 * (π / 9) = 2 * (2 * (π / 9)) by ring]
        rw [sin_two_mul]
        <;> ring_nf
      have h1000 : sin (2 * (π / 9)) = 2 * sin (π / 9) * cos (π / 9) := by
        rw [show 2 * (π / 9) = 2 * (π / 9) by ring]
        rw [sin_two_mul]
        <;> ring_nf
      rw [h10, h100, h1000]
      ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h4]
    field_simp [h1]
    <;> ring_nf
    <;> norm_num
    <;> field_simp [h1]
  have h3 : sin (8 * (π / 9)) = sin (π - (π / 9)) := by
    ring_nf
  have h4 : sin (π - (π / 9)) = sin (π / 9) := by
    rw [sin_pi_sub]
  rw [h2, h3, h4]
  field_simp [h1]
  <;> ring_nf
  <;> norm_num
  <;> field_simp [h1]
  <;> ring_nf
  <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> ring_nf
  <;> norm_num