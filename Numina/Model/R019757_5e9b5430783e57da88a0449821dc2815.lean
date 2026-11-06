import Mathlib

open Real

theorem inequalities_180058 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (2 * sqrt (a * b)) / (sqrt a + sqrt b) ≤ (a * b) ^ ((1 : ℝ) / 4) := by
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hab : 0 < a * b := mul_pos ha hb
  have h3 : sqrt a + sqrt b > 0 := by
    have h4 : sqrt a ≥ 0 := Real.sqrt_nonneg a
    have h5 : sqrt b > 0 := by
      apply Real.sqrt_pos.mpr
      exact hb
    linarith [h4, h5]
  have h1 : sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  have h2 : sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have h6 : sqrt (a * b) = sqrt a * sqrt b := by
    rw [Real.sqrt_mul (by linarith)]
  have h4 : (a * b) ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt (a * b)) := by
    have h5 : Real.sqrt (Real.sqrt (a * b)) = (Real.sqrt (a * b)) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      all_goals norm_num
    rw [h5]
    have h6 : Real.sqrt (a * b) = (a * b) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      all_goals norm_num
    rw [h6]
    rw [← Real.rpow_mul]
    norm_num
    all_goals positivity
  rw [h4]
  have h7 : (2 * sqrt (a * b) ) / (sqrt a + sqrt b) ≥ 0 := by
    apply div_nonneg
    · -- Show that 2 * sqrt (a * b) ≥ 0
      nlinarith [show sqrt (a * b) ≥ 0 by positivity, Real.sqrt_nonneg (a * b)]
    · -- Show that sqrt a + sqrt b ≥ 0
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have h8 : Real.sqrt (Real.sqrt (a * b)) ≥ 0 := Real.sqrt_nonneg _
  have h5 : ( (2 * sqrt (a * b) ) / (sqrt a + sqrt b) ) ^ 2 ≤ (Real.sqrt (Real.sqrt (a * b)) ) ^ 2 := by
    have h9 : ( (2 * sqrt (a * b) ) / (sqrt a + sqrt b) ) ^ 2 = 4 * (a * b) / ( (sqrt a + sqrt b) ^ 2 ) := by
      have h6' : sqrt (a * b) = sqrt a * sqrt b := by
        rw [Real.sqrt_mul (by linarith)]
      rw [h6']
      field_simp [show sqrt a + sqrt b ≠ 0 by positivity, h1, h2, mul_pos ha hb]
      <;> nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg (sqrt a - sqrt b)]
    have h15 : (Real.sqrt (Real.sqrt (a * b)) ) ^ 2 = Real.sqrt (a * b) := by
      rw [Real.sq_sqrt]
      positivity
    rw [h9, h15]
    have h10 : (sqrt a + sqrt b) ^ 2 = a + b + 2 * (sqrt a * sqrt b) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith)]
    have h11 : sqrt a * sqrt b = Real.sqrt (a * b) := by
      rw [← Real.sqrt_mul (by linarith)]
    have h10' : (sqrt a + sqrt b) ^ 2 = a + b + 2 * Real.sqrt (a * b) := by
      rw [h10, h11]
    have h13 : 4 * (a * b) ≤ Real.sqrt (a * b) * ( (sqrt a + sqrt b) ^ 2 ) := by
      rw [h10']
      nlinarith [sq_nonneg (sqrt a - sqrt b), Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), Real.sq_sqrt (show 0 ≤ (a * b : ℝ) by positivity), sq_nonneg (sqrt a ^ 2 - sqrt b ^ 2), sq_nonneg (sqrt a - sqrt b), mul_nonneg (show 0 ≤ (sqrt a : ℝ) by positivity) (show 0 ≤ (sqrt b : ℝ) by positivity), mul_pos ha hb, sq_nonneg (Real.sqrt (a * b) - (sqrt a * sqrt b)), sq_nonneg (sqrt a * sqrt b - Real.sqrt (a * b)), Real.sqrt_nonneg (a * b)]
    have h17 : 4 * (a * b) / ( (sqrt a + sqrt b) ^ 2 ) ≤ Real.sqrt (a * b) := by
      have h14 : (sqrt a + sqrt b) ^ 2 > 0 := by positivity
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [h13, Real.sqrt_nonneg (a * b)]
    linarith [h17, Real.sqrt_nonneg (a * b)]
  have h9 : ( (2 * sqrt (a * b) ) / (sqrt a + sqrt b) ) ≤ Real.sqrt (Real.sqrt (a * b)) := by
    nlinarith [h5, Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (Real.sqrt (a * b)), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (a), Real.sqrt_nonneg (b), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  linarith [h9]