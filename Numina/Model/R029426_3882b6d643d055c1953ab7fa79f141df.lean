import Mathlib

theorem inequalities_224585 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * √a + 3 * b ^ ((1 : ℝ) / 3) ≥ 5 * (a * b) ^ ((1 : ℝ) / 5) := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : (a ^ (1 / 2 : ℝ)) ^ (2 / 5 : ℝ) = a ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_mul]
    norm_num
    all_goals nlinarith
  have h4 : (b ^ (1 / 3 : ℝ)) ^ (3 / 5 : ℝ) = b ^ (1 / 5 : ℝ) := by 
    rw [← Real.rpow_mul]
    norm_num
    all_goals nlinarith
  have h5 : (a ^ (1 / 2 : ℝ)) ^ (2 / 5 : ℝ) * (b ^ (1 / 3 : ℝ)) ^ (3 / 5 : ℝ) = (a * b) ^ (1 / 5 : ℝ) := by 
    rw [h3, h4]
    have h6 : a ^ (1 / 5 : ℝ) * b ^ (1 / 5 : ℝ) = (a * b) ^ (1 / 5 : ℝ) := by 
      rw [← Real.mul_rpow]
      all_goals nlinarith
    linarith [h6]
  have h7 : (a ^ (1 / 2 : ℝ) : ℝ) ≥ 0 := by positivity
  have h8 : (b ^ (1 / 3 : ℝ) : ℝ) ≥ 0 := by positivity
  have h9 : (a ^ (1 / 2 : ℝ) ) ^ (2 / 5 : ℝ) * (b ^ (1 / 3 : ℝ) ) ^ (3 / 5 : ℝ) ≤ (2 / 5 * (a ^ (1 / 2 : ℝ)) + 3 / 5 * (b ^ (1 / 3 : ℝ)) ) := by 
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
    try positivity
    all_goals norm_num
  have h10 : 2 * √a + 3 * b ^ ((1 : ℝ) / 3) ≥ 5 * (a * b) ^ ((1 : ℝ) / 5) := by 
    have h11 : √a = a ^ (1 / 2 : ℝ) := by 
      rw [Real.sqrt_eq_rpow]
    rw [h11]
    have h12 : (2 / 5 * (a ^ (1 / 2 : ℝ)) + 3 / 5 * (b ^ (1 / 3 : ℝ)) ) = (2 * a ^ (1 / 2 : ℝ) + 3 * b ^ (1 / 3 : ℝ) ) / 5 := by ring
    rw [h12] at h9
    have h13 : (a ^ (1 / 2 : ℝ) ) ^ (2 / 5 : ℝ) * (b ^ (1 / 3 : ℝ) ) ^ (3 / 5 : ℝ) = (a * b) ^ (1 / 5 : ℝ) := h5
    rw [h13] at h9
    have h14 : 5 * ((a * b) ^ (1 / 5 : ℝ)) ≤ 5 * ((2 * a ^ (1 / 2 : ℝ) + 3 * b ^ (1 / 3 : ℝ) ) / 5 ) := by 
      linarith [h9]
    have h15 : 5 * ((2 * a ^ (1 / 2 : ℝ) + 3 * b ^ (1 / 3 : ℝ) ) / 5 ) = 2 * a ^ (1 / 2 : ℝ) + 3 * b ^ (1 / 3 : ℝ) := by 
      ring
    rw [h15] at h14
    linarith [h14]
  exact h10