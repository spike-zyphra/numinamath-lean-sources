import Mathlib

theorem inequalities_602620 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * Real.sqrt a + 3 * b ^ ((1 : ℝ) / 3) ≥ 5 * (a * b) ^ ((1 : ℝ) / 5) := by
  have h6 : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a
  have h7 : b ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
  have h8 : (2 : ℝ) / 5 + (3 : ℝ) / 5 = 1 := by norm_num
  have h9 : ((Real.sqrt a) ^ (2 / 5 : ℝ)) * ((b ^ ((1 : ℝ) / 3)) ^ (3 / 5 : ℝ)) ≤ (2 / 5 : ℝ) * (Real.sqrt a) + (3 / 5 : ℝ) * (b ^ ((1 : ℝ) / 3)) := by
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals nlinarith
    all_goals nlinarith
  have h10 : ((Real.sqrt a) ^ (2 / 5 : ℝ)) * ((b ^ ((1 : ℝ) / 3)) ^ (3 / 5 : ℝ)) = (a * b) ^ ((1 : ℝ) / 5) := by
    have h11 : (Real.sqrt a) ^ (2 / 5 : ℝ) = (a) ^ (1 / 5 : ℝ) := by
      have h21 : Real.sqrt a = (a) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h21]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h12 : (b ^ ((1 : ℝ) / 3)) ^ (3 / 5 : ℝ) = (b) ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h13 : (a) ^ (1 / 5 : ℝ) * (b) ^ (1 / 5 : ℝ) = (a * b) ^ (1 / 5 : ℝ) := by
      rw [← Real.mul_rpow]
      all_goals nlinarith
    rw [h11, h12]
    nlinarith [h13]
  nlinarith [h9, h10]