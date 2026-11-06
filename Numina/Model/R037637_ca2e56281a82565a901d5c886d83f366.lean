import Mathlib


theorem inequalities_217126 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * Real.sqrt a + 3 * (b ^ ((1 : ℝ) / 3)) ≥ 5 * (a * b) ^ ((1 : ℝ) / 5) := by
  have h1 : Real.sqrt a ≥ 0 := by positivity
  have h2 : b ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
  have h3 : (a * b) ^ ((1 : ℝ) / 5) ≥ 0 := by positivity

  have h4 : Real.sqrt a = a ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]

  have h5 : (a ^ ((1 : ℝ) / 2)) ^ (2 / 5 : ℝ) = a ^ ((1 / 5 : ℝ)) := by
    rw [← Real.rpow_mul]
    ring_nf
    all_goals positivity

  have h6 : (b ^ ((1 : ℝ) / 3)) ^ (3 / 5 : ℝ) = b ^ ((1 / 5 : ℝ)) := by
    rw [← Real.rpow_mul]
    ring_nf
    all_goals positivity

  have h7 : (2 / 5 : ℝ) * (Real.sqrt a) + (3 / 5 : ℝ) * (b ^ ((1 : ℝ) / 3)) ≥ (Real.sqrt a) ^ (2 / 5 : ℝ) * ((b ^ ((1 : ℝ) / 3)) ^ (3 / 5 : ℝ)) := by
    have h8 : (Real.sqrt a : ℝ) ≥ 0 := by positivity
    have h9 : (b ^ ((1 : ℝ) / 3) : ℝ) ≥ 0 := by positivity
    have h10 : (2 / 5 : ℝ) + (3 / 5 : ℝ) = 1 := by norm_num
    have h11 : (Real.sqrt a) ^ (2 / 5 : ℝ) ≥ 0 := by positivity
    have h12 : (b ^ ((1 : ℝ) / 3)) ^ (3 / 5 : ℝ) ≥ 0 := by positivity
    have h13 : (Real.sqrt a) ^ (2 / 5 : ℝ) * ((b ^ ((1 : ℝ) / 3)) ^ (3 / 5 : ℝ)) ≤ (2 / 5 : ℝ) * (Real.sqrt a) + (3 / 5 : ℝ) * (b ^ ((1 : ℝ) / 3)) := by
      apply Real.geom_mean_le_arith_mean2_weighted
      all_goals
        try linarith
        try positivity
    linarith

  have h14 : (a ^ ((1 : ℝ) / 5)) ≥ 0 := by positivity
  have h15 : (b ^ ((1 : ℝ) / 5)) ≥ 0 := by positivity

  have h16 : (Real.sqrt a) ^ (2 / 5 : ℝ) * ((b ^ ((1 : ℝ) / 3)) ^ (3 / 5 : ℝ)) = (a * b) ^ ((1 : ℝ) / 5) := by
    have h17 : (Real.sqrt a) ^ (2 / 5 : ℝ) = a ^ ((1 : ℝ) / 5) := by
      rw [show Real.sqrt a = a ^ ((1 : ℝ) / 2) by rw [Real.sqrt_eq_rpow]]
      rw [h5]

    have h18 : (b ^ ((1 : ℝ) / 3)) ^ (3 / 5 : ℝ) = b ^ ((1 : ℝ) / 5) := by
      rw [h6]

    rw [h17, h18]
    have h19 : a ^ ((1 : ℝ) / 5) * b ^ ((1 : ℝ) / 5) = (a * b) ^ ((1 : ℝ) / 5) := by
      rw [← Real.mul_rpow]
      all_goals nlinarith [show 0 ≤ a by linarith, show 0 ≤ b by linarith]
    linarith [h19]

  have h8 : 2 * Real.sqrt a + 3 * (b ^ ((1 : ℝ) / 3)) = 5 * ((2 / 5 : ℝ) * (Real.sqrt a) + (3 / 5 : ℝ) * (b ^ ((1 : ℝ) / 3)))
      := by ring

  linarith [h8, h7, h16]