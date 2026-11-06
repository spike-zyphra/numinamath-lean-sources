import Mathlib

open Real

theorem inequalities_5159 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  (b + c) / sqrt (b^2 + b * c + c^2) +
  (c + a) / sqrt (c^2 + c * a + a^2) +
  (a + b) / sqrt (a^2 + a * b + b^2) ≤ 2 * sqrt 3 := by
  have h1 : (b + c) / sqrt (b^2 + b * c + c^2) ≤ 2 / Real.sqrt 3 := by
    have h5 : (b + c) * Real.sqrt 3 ≤ 2 * sqrt (b^2 + b * c + c^2) := by
      have h6 : ((b + c) * Real.sqrt 3) ^ 2 ≤ (2 * sqrt (b^2 + b * c + c^2)) ^ 2 := by
        have h7 : ((b + c) * Real.sqrt 3) ^ 2 = (b + c) ^ 2 * (Real.sqrt 3) ^ 2 := by ring
        have h8 : (2 * sqrt (b^2 + b * c + c^2)) ^ 2 = 4 * (sqrt (b^2 + b * c + c^2)) ^ 2 := by ring
        rw [h7, h8]
        have h9 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        rw [h9]
        have h10 : (sqrt (b^2 + b * c + c^2)) ^ 2 = b^2 + b * c + c^2 := by
          rw [Real.sq_sqrt]
          positivity
        rw [h10]
        nlinarith [sq_nonneg (b - c)]
      have h6' : (b + c) * Real.sqrt 3 ≤ 2 * sqrt (b^2 + b * c + c^2) := by
        nlinarith [show 0 ≤ 2 * sqrt (b^2 + b * c + c^2) by positivity, show 0 ≤ (b + c) * Real.sqrt 3 by positivity, h6]
      linarith
    have h8 : (b + c) / sqrt (b^2 + b * c + c^2) ≤ 2 / Real.sqrt 3 := by
      have h9 : sqrt (b^2 + b * c + c^2) > 0 := by positivity
      have h10 : Real.sqrt 3 > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h5]
    exact h8
  have h2 : (c + a) / sqrt (c^2 + c * a + a^2) ≤ 2 / Real.sqrt 3 := by
    have h5 : (c + a) * Real.sqrt 3 ≤ 2 * sqrt (c^2 + c * a + a^2) := by
      have h6 : ((c + a) * Real.sqrt 3) ^ 2 ≤ (2 * sqrt (c^2 + c * a + a^2)) ^ 2 := by
        have h7 : ((c + a) * Real.sqrt 3) ^ 2 = (c + a) ^ 2 * (Real.sqrt 3) ^ 2 := by ring
        have h8 : (2 * sqrt (c^2 + c * a + a^2)) ^ 2 = 4 * (sqrt (c^2 + c * a + a^2)) ^ 2 := by ring
        rw [h7, h8]
        have h9 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        rw [h9]
        have h10 : (sqrt (c^2 + c * a + a^2)) ^ 2 = c^2 + c * a + a^2 := by
          rw [Real.sq_sqrt]
          positivity
        rw [h10]
        nlinarith [sq_nonneg (c - a)]
      have h6' : (c + a) * Real.sqrt 3 ≤ 2 * sqrt (c^2 + c * a + a^2) := by
        nlinarith [show 0 ≤ 2 * sqrt (c^2 + c * a + a^2) by positivity, show 0 ≤ (c + a) * Real.sqrt 3 by positivity, h6]
      linarith
    have h8 : (c + a) / sqrt (c^2 + c * a + a^2) ≤ 2 / Real.sqrt 3 := by
      have h9 : sqrt (c^2 + c * a + a^2) > 0 := by positivity
      have h10 : Real.sqrt 3 > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h5]
    exact h8
  have h3 : (a + b) / sqrt (a^2 + a * b + b^2) ≤ 2 / Real.sqrt 3 := by
    have h5 : (a + b) * Real.sqrt 3 ≤ 2 * sqrt (a^2 + a * b + b^2) := by
      have h6 : ((a + b) * Real.sqrt 3) ^ 2 ≤ (2 * sqrt (a^2 + a * b + b^2)) ^ 2 := by
        have h7 : ((a + b) * Real.sqrt 3) ^ 2 = (a + b) ^ 2 * (Real.sqrt 3) ^ 2 := by ring
        have h8 : (2 * sqrt (a^2 + a * b + b^2)) ^ 2 = 4 * (sqrt (a^2 + a * b + b^2)) ^ 2 := by ring
        rw [h7, h8]
        have h9 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        rw [h9]
        have h10 : (sqrt (a^2 + a * b + b^2)) ^ 2 = a^2 + a * b + b^2 := by
          rw [Real.sq_sqrt]
          positivity
        rw [h10]
        nlinarith [sq_nonneg (a - b)]
      have h6' : (a + b) * Real.sqrt 3 ≤ 2 * sqrt (a^2 + a * b + b^2) := by
        nlinarith [show 0 ≤ 2 * sqrt (a^2 + a * b + b^2) by positivity, show 0 ≤ (a + b) * Real.sqrt 3 by positivity, h6]
      linarith
    have h8 : (a + b) / sqrt (a^2 + a * b + b^2) ≤ 2 / Real.sqrt 3 := by
      have h9 : sqrt (a^2 + a * b + b^2) > 0 := by positivity
      have h10 : Real.sqrt 3 > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h5]
    exact h8
  have h9 : (b + c) / sqrt (b^2 + b * c + c^2) +
    (c + a) / sqrt (c^2 + c * a + a^2) +
    (a + b) / sqrt (a^2 + a * b + b^2) ≤ 3 * (2 / Real.sqrt 3) := by 
    have h10 : (b + c) / sqrt (b^2 + b * c + c^2) ≤ 2 / Real.sqrt 3 := h1
    have h11 : (c + a) / sqrt (c^2 + c * a + a^2) ≤ 2 / Real.sqrt 3 := h2
    have h12 : (a + b) / sqrt (a^2 + a * b + b^2) ≤ 2 / Real.sqrt 3 := h3
    linarith
  have h10 : 3 * (2 / Real.sqrt 3) = 2 * Real.sqrt 3 := by
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  nlinarith [h10, h9]