import Mathlib

open Real Set
open scoped Real

theorem algebra_321439 : tan (22.5 * π / 180) = sqrt 2 - 1 := by
  have h1 : 22.5 * π / 180 = π / 8 := by ring_nf
  rw [h1]
  have h4 : Real.cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h10 : tan (π / 8) ^ 2 = (1 - Real.cos (π / 4)) / (1 + Real.cos (π / 4)) := by
    have htan2 : tan (π / 8) ^ 2 = Real.sin (π / 8) ^ 2 / Real.cos (π / 8) ^ 2 := by
      rw [tan_eq_sin_div_cos]
      <;> ring_nf <;> field_simp <;> ring_nf
    have hsin_sq : Real.sin (π / 8) ^ 2 = 1 - Real.cos (π / 8) ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq (π / 8)]
      ring_nf
    have hcos_sq : Real.cos (π / 8) ^ 2 = (1 + Real.cos (π / 4)) / 2 := by
      have hcos2 : Real.cos (π / 4) = 2 * Real.cos (π / 8) ^ 2 - 1 := by
        rw [← Real.cos_two_mul (π / 8)]
        ring_nf
      linarith [hcos2]
    rw [htan2, hsin_sq, hcos_sq]
    <;> field_simp [(show 1 + Real.cos (π / 4) ≠ 0 by
        nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    ), Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    <;> ring_nf <;> field_simp <;> ring_nf <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, sq_nonneg (Real.cos (π/8)), sq_nonneg (Real.sin (π/8)), Real.pi_pos]
  rw [h4] at h10
  have h11 : tan (π / 8) ^ 2 = 3 - 2 * Real.sqrt 2 := by
    have h12 : tan (π / 8) ^ 2 = (1 - Real.sqrt 2 / 2) / (1 + Real.sqrt 2 / 2) := by
      linarith [h10, h4]
    have h13 : (1 - Real.sqrt 2 / 2) / (1 + Real.sqrt 2 / 2) = 3 - 2 * Real.sqrt 2 := by
      have hsqrt2_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := by nlinarith [hsqrt2_pos]
      have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      field_simp [(show (1 + Real.sqrt 2 / 2 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      ) , hsqrt2_nonneg, hsqrt2_sq]
      <;> ring_nf <;> nlinarith [sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    linarith [h12, h13]
  have htan_pos : tan (π / 8) > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h14 : tan (π / 8) = Real.sqrt (3 - 2 * Real.sqrt 2) := by
    have h15 : Real.sqrt (tan (π / 8) ^ 2) = tan (π / 8) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_pos htan_pos]
    rw [←h15]
    rw [h11]
  rw [h14]
  have h12 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
    have h13 : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h14 : Real.sqrt ((Real.sqrt 2 - 1) ^ 2) = Real.sqrt 2 - 1 := by
      rw [Real.sqrt_sq_eq_abs]
      have h15 : Real.sqrt 2 ≥ 1 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      have h16 : (Real.sqrt 2 - 1) ≥ 0 := by linarith [h15]
      rw [abs_of_nonneg h16]
    have h15 : Real.sqrt ((Real.sqrt 2 - 1) ^ 2) = Real.sqrt (3 - 2 * Real.sqrt 2) := by
      rw [h13]
    rw [h15] at h14
    linarith [h14]
  exact h12