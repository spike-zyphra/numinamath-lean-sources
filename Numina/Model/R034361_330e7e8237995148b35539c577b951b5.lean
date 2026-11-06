import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_23015 (x y z : ℝ) (hx : x = 4) (hy : y = 4) (hz : z = 4 * sqrt 6) :
    (8 * sqrt 2, π / 4, π / 6) = (sqrt (x^2 + y^2 + z^2), arctan (y / x), arccos (z / sqrt (x^2 + y^2 + z^2))) := by
  rw [hx, hy, hz]
  have h1 : sqrt ((4 : ℝ) ^ 2 + (4 : ℝ) ^ 2 + (4 * sqrt 6) ^ 2) = 8 * sqrt 2 := by
    have h2 : (4 : ℝ) ^ 2 + (4 : ℝ) ^ 2 + (4 * sqrt 6) ^ 2 = (128 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
    rw [h2]
    have h3 : sqrt ((128 : ℝ)) = 8 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    linarith

  have h2 : arctan ((4 : ℝ) / (4 : ℝ)) = Real.pi / 4 := by
    norm_num [arctan_one]

  have h5' : (4 * sqrt 6 : ℝ) / sqrt ((4 : ℝ) ^ 2 + (4 : ℝ) ^ 2 + (4 * Real.sqrt 6) ^ 2) = Real.sqrt 3 / 2 := by
    rw [h1]
    have h4 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      rw [← Real.sqrt_mul (by norm_num)]
      norm_num
    have h5 : (4 * sqrt 6 : ℝ) / (8 * sqrt 2) = Real.sqrt 3 / 2 := by
      rw [h4]
      have h5 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      have h6 : Real.sqrt 3 ^ 2 = (3 : ℝ) := by 
        rw [Real.sq_sqrt]
        norm_num
      field_simp [show (8 * Real.sqrt 2 : ℝ) ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]]
      <;> ring_nf <;> norm_num [h5, h6]
      <;> ring_nf <;> norm_num [h5, h6]
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6]
      all_goals linarith
    linarith
  -- To compute $\phi$
  have h6' : Real.arccos (Real.sqrt 3 / 2) = Real.pi / 6 := by
    have h10 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
      rw [Real.cos_pi_div_six]
      all_goals linarith
    -- Since arccos (cos (π/6)) = π/6 and cos (π/6) = sqrt 3 / 2
    have h11 : Real.arccos (Real.cos (Real.pi / 6)) = Real.pi / 6 := by
      rw [Real.arccos_cos]
      all_goals linarith [Real.pi_pos]
      all_goals linarith [Real.pi_pos]
    have h12 : Real.sqrt 3 / 2 = Real.cos (Real.pi / 6) := by
      linarith [h10]
    rw [h12] at *
    all_goals
    try { 
      have h7 : Real.pi / 6 ≥ (0 : ℝ) := by 
        nlinarith [Real.pi_pos]
      have h8 : Real.pi / 6 ≤ (Real.pi : ℝ) := by 
        nlinarith [Real.pi_pos]
      all_goals
      try { tauto }
      try { nlinarith [Real.pi_pos] }
    }
    all_goals linarith
  simp_all [h1, h2, h5', h6']
  <;> norm_num [Real.sqrt_pos.mpr]
  <;> ring_nf
  <;> norm_num [Real.sq_sqrt]
  <;> ring_nf
  <;> norm_num [Real.sq_sqrt]
  <;> ring_nf
  <;> norm_num [Real.sq_sqrt]
  <;> ring_nf <;> norm_num [Real.sq_sqrt] <;> nlinarith [Real.pi_gt_three]