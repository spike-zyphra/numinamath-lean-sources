import Mathlib

theorem inequalities_185150 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) ≥ Real.sqrt 5 := by
  have h1 : b = 1 - a := by linarith
  have h3 : (Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2)) ^ 2 ≥ 5 := by
    have ha2 : 0 < a := by linarith [ha]
    have hb2 : 0 < b := by linarith [hb]
    have ha3 : (Real.sqrt (1 + a ^ 2)) ^ 2 = 1 + a ^ 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have hb3 : (Real.sqrt (1 + b ^ 2)) ^ 2 = 1 + b ^ 2 := by
      rw [Real.sq_sqrt]
      nlinarith [sq_nonneg b, h]
    -- Prove that (sqrt(1+a^2) + sqrt(1+b^2))^2 >= 5
    have h4 : (Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2)) ^ 2 =
        (Real.sqrt (1 + a ^ 2)) ^ 2 + (Real.sqrt (1 + b ^ 2)) ^ 2 + 2 * (Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2)) := by ring
    rw [h4]
    rw [ha3, hb3]
    have h5 : a * b ≤ (1 / 4) := by
      have h7 : b = 1 - a := by linarith
      rw [h7]
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a), sq_nonneg (1 - a), mul_pos ha (show 0 < (1 - a : ℝ) by nlinarith)]
    -- Prove that (1+a^2)(1+b^2) >= 1/4
    have h6 : (1 + a ^ 2) * (1 + b ^ 2) ≥ 1 / 4 := by
      have h7 : a * b ≤ (1 / 4) := h5
      have h8 : b = 1 - a := by linarith
      rw [h8]
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a * (1 - a) - 1 / 4), sq_nonneg (a + (1 - a) - 1), sq_nonneg (a - (1 - a)), sq_nonneg (a * (1 - a)), mul_pos ha (show 0 < (1 - a : ℝ) by nlinarith)]
    -- Prove that sqrt(1+a^2) * sqrt(1+b^2) >= 1/2
    have h60 : Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2) ≥ (1 / 2 : ℝ) := by
      have h50 : Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2)) = Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2) := by
        rw [← Real.sqrt_mul (by positivity)]
        <;> ring_nf <;> norm_num
      have h70 : Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2) = Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2)) := by
        rw [h50]
      have h80 : Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2)) ≥ Real.sqrt (1 / 4 : ℝ) := Real.sqrt_le_sqrt (by linarith [h6])
      have h11 : Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h610 : Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2) ≥ (1 / 2 : ℝ) := by
        rw [h70]
        linarith [h80, h11]
      exact h610
    -- Now, prove final inequality
    nlinarith [Real.sqrt_nonneg (1 + a ^ 2), Real.sqrt_nonneg (1 + b ^ 2), sq_nonneg (Real.sqrt (1 + a ^ 2) - Real.sqrt (1 + b ^ 2)), sq_nonneg (a - b), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + a ^ 2 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + b ^ 2 : ℝ) by positivity), h60, mul_pos ha hb, h1, ha, hb]
  -- Prove from h3 that sqrt(1+a^2) + sqrt(1+b^2) >= sqrt(5)
  have h4 : Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) ≥ 0 := by positivity
  have h500 : (Real.sqrt 5 : ℝ) ≥ 0 := by positivity
  have h510 : Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) ≥ Real.sqrt 5 := by
    have h8 : (Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2)) ^ 2 ≥ (Real.sqrt 5) ^ 2 := by
      linarith [h3, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h9 : Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) ≥ 0 := by positivity
    have h10 : Real.sqrt (5 : ℝ) ≥ 0 := by positivity
    nlinarith [h8, h9, h10, Real.sqrt_nonneg (1 + a ^ 2), Real.sqrt_nonneg (1 + b ^ 2), Real.sqrt_nonneg (5 : ℝ)]
  linarith [h510, Real.sqrt_nonneg (1 + a ^ 2), Real.sqrt_nonneg (1 + b ^ 2), Real.sqrt_nonneg (5 : ℝ)]