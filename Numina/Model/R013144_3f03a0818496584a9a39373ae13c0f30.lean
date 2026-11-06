import Mathlib

theorem inequalities_129131 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.sqrt (a^2 + b^2) + Real.sqrt (b^2 + c^2) + Real.sqrt (c^2 + d^2) +
    Real.sqrt (d^2 + a^2) ≥
    Real.sqrt 2 * (a + b + c + d) := by
  have h1 : Real.sqrt (a^2 + b^2) ≥ Real.sqrt 2 / 2 * (a + b) := by
    have h2 : 0 ≤ a := by linarith
    have h3 : 0 ≤ b := by linarith
    have h4 : Real.sqrt (a^2 + b^2) ≥ Real.sqrt 2 / 2 * (a + b) := by
      have h5 : (Real.sqrt (a^2 + b^2)) ^ 2 ≥ (Real.sqrt 2 / 2 * (a + b)) ^ 2 := by
        have h6 : (Real.sqrt (a^2 + b^2)) ^ 2 = a^2 + b^2 := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : (Real.sqrt 2 / 2 * (a + b)) ^ 2 = (Real.sqrt 2) ^ 2 / 4 * (a + b) ^ 2 := by
          ring_nf
        rw [h6, h7]
        nlinarith [sq_nonneg (a - b), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      have h8 : 0 ≤ Real.sqrt 2 / 2 * (a + b) := by
        have h9 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h10 : 0 ≤ a + b := by linarith
        nlinarith
      have h11 : 0 ≤ Real.sqrt (a^2 + b^2) := by
        apply Real.sqrt_nonneg
      nlinarith [Real.sqrt_nonneg (a^2 + b^2), Real.sqrt_nonneg 2]
    linarith
  have h2 : Real.sqrt (b^2 + c^2) ≥ Real.sqrt 2 / 2 * (b + c) := by
    have h3 : 0 ≤ b := by linarith
    have h4 : 0 ≤ c := by linarith
    have h4 : Real.sqrt (b^2 + c^2) ≥ Real.sqrt 2 / 2 * (b + c) := by
      have h5 : (Real.sqrt (b^2 + c^2)) ^ 2 ≥ (Real.sqrt 2 / 2 * (b + c)) ^ 2 := by
        have h6 : (Real.sqrt (b^2 + c^2)) ^ 2 = b^2 + c^2 := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : (Real.sqrt 2 / 2 * (b + c)) ^ 2 = (Real.sqrt 2) ^ 2 / 4 * (b + c) ^ 2 := by
          ring_nf
        rw [h6, h7]
        nlinarith [sq_nonneg (b - c), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      have h8 : 0 ≤ Real.sqrt 2 / 2 * (b + c) := by
        have h9 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h10 : 0 ≤ b + c := by linarith
        nlinarith
      have h11 : 0 ≤ Real.sqrt (b^2 + c^2) := by
        apply Real.sqrt_nonneg
      nlinarith [Real.sqrt_nonneg (b^2 + c^2), Real.sqrt_nonneg 2]
    linarith
  have h3 : Real.sqrt (c^2 + d^2) ≥ Real.sqrt 2 / 2 * (c + d) := by
    have h4 : 0 ≤ c := by linarith
    have h5 : 0 ≤ d := by linarith
    have h4 : Real.sqrt (c^2 + d^2) ≥ Real.sqrt 2 / 2 * (c + d) := by
      have h5 : (Real.sqrt (c^2 + d^2)) ^ 2 ≥ (Real.sqrt 2 / 2 * (c + d)) ^ 2 := by
        have h6 : (Real.sqrt (c^2 + d^2)) ^ 2 = c^2 + d^2 := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : (Real.sqrt 2 / 2 * (c + d)) ^ 2 = (Real.sqrt 2) ^ 2 / 4 * (c + d) ^ 2 := by
          ring_nf
        rw [h6, h7]
        nlinarith [sq_nonneg (c - d), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      have h8 : 0 ≤ Real.sqrt 2 / 2 * (c + d) := by
        have h9 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h10 : 0 ≤ c + d := by linarith
        nlinarith
      have h11 : 0 ≤ Real.sqrt (c^2 + d^2) := by
        apply Real.sqrt_nonneg
      nlinarith [Real.sqrt_nonneg (c^2 + d^2), Real.sqrt_nonneg 2]
    linarith
  have h4 : Real.sqrt (d^2 + a^2) ≥ Real.sqrt 2 / 2 * (d + a) := by
    have h4 : 0 ≤ d := by linarith
    have h5 : 0 ≤ a := by linarith
    have h4 : Real.sqrt (d^2 + a^2) ≥ Real.sqrt 2 / 2 * (d + a) := by
      have h5 : (Real.sqrt (d^2 + a^2)) ^ 2 ≥ (Real.sqrt 2 / 2 * (d + a)) ^ 2 := by
        have h6 : (Real.sqrt (d^2 + a^2)) ^ 2 = d^2 + a^2 := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : (Real.sqrt 2 / 2 * (d + a)) ^ 2 = (Real.sqrt 2) ^ 2 / 4 * (d + a) ^ 2 := by
          ring_nf
        rw [h6, h7]
        nlinarith [sq_nonneg (d - a), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      have h8 : 0 ≤ Real.sqrt 2 / 2 * (d + a) := by
        have h9 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h10 : 0 ≤ d + a := by linarith
        nlinarith
      have h11 : 0 ≤ Real.sqrt (d^2 + a^2) := by
        apply Real.sqrt_nonneg
      nlinarith [Real.sqrt_nonneg (d^2 + a^2), Real.sqrt_nonneg 2]
    linarith
  have h5 : Real.sqrt (a^2 + b^2) + Real.sqrt (b^2 + c^2) + Real.sqrt (c^2 + d^2) + Real.sqrt (d^2 + a^2) ≥ 
           Real.sqrt 2 * (a + b + c + d) := by
    nlinarith [h1, h2, h3, h4, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  exact h5