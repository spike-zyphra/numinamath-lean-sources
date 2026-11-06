import Mathlib
open Real

theorem algebra_98026 {x : ℝ} (hx : x = cos (36 * π / 180) - cos (72 * π / 180)) : x = 1 / 2 := by
  rw [hx]
  have h1 : cos (36 * π / 180) = cos (π / 5) := by
    have h2 : 36 * π / 180 = (π / 5) := by
      ring_nf
      <;> field_simp [Real.pi_pos]
      <;> ring
    rw [h2]
  have h3 : cos (72 * π / 180) = cos (2 * (π / 5)) := by
    have h4 : 72 * π / 180 = (2 * (π / 5)) := by
      ring_nf
      <;> field_simp [Real.pi_pos]
      <;> ring
    rw [h4]
  rw [h1, h3]
  have h4 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by
    have h5 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by
      rw [cos_pi_div_five]
      <;> ring_nf
      <;> field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    exact h5
  have h5 : cos (2 * (π / 5)) = (Real.sqrt 5 - 1) / 4 := by
    have h6 : cos (2 * (π / 5)) = 2 * cos (π / 5)^2 - 1 := by
      rw [← cos_two_mul]
      <;> ring_nf <;> ring
    rw [h6, h4]
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5  : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5  : ℝ) by norm_num)]
  rw [h4, h5]
  field_simp
  <;> ring_nf
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5  : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5  : ℝ) by norm_num)]