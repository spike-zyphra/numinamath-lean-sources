import Mathlib

open Real

theorem inequalities_28304 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    2 / ((a + b) * (c + d)) ≤ 1 / sqrt (a * b) + 1 / sqrt (c * d) := by

  have h1 : sqrt (a * b) ≤ (a + b) / 2 := by
    have hab : 0 < a * b := mul_pos ha hb
    have h11 : sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      rw [Real.sqrt_mul (by linarith)]
    have h21 : (Real.sqrt a * Real.sqrt b) ≤ (a + b) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
        Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), 
        sq_nonneg (a - b)]
    linarith [h11, h21]
  
  have h3 : sqrt (c * d) ≤ (c + d) / 2 := by
    have hcd : 0 < c * d := mul_pos hc hd
    have h11 : sqrt (c * d) = Real.sqrt c * Real.sqrt d := by
      rw [Real.sqrt_mul (by linarith)]
    have h21 : (Real.sqrt c * Real.sqrt d) ≤ (c + d) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt c - Real.sqrt d), Real.sqrt_nonneg c, Real.sqrt_nonneg d, 
        Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (d : ℝ) by linarith), 
        sq_nonneg (c - d)]
    linarith [h11, h21]

  have h2 : 1 / sqrt (a * b) ≥ 2 / (a + b) := by
    have hab : 0 < a * b := mul_pos ha hb
    have h11 : sqrt (a * b) > 0 := by positivity
    have h14 : sqrt (a * b) ≤ (a + b) / 2 := h1
    have h21 : (1 / sqrt (a * b) : ℝ) ≥ (2 / (a + b) : ℝ) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [show sqrt (a * b) > 0 by positivity, show a + b > 0 by nlinarith, h14]
    linarith

  have h4 : 1 / sqrt (c * d) ≥ 2 / (c + d) := by
    have hcd : 0 < c * d := mul_pos hc hd
    have h11 : sqrt (c * d) > 0 := by positivity
    have h14 : sqrt (c * d) ≤ (c + d) / 2 := h3
    have h21 : (1 / sqrt (c * d) : ℝ) ≥ (2 / (c + d) : ℝ) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [show sqrt (c * d) > 0 by positivity, show c + d > 0 by nlinarith, h14]
    linarith

  have h5 : (1 / sqrt (a * b) + 1 / sqrt (c * d) : ℝ) ≥ (2 / (a + b) + 2 / (c + d) : ℝ) := by
    linarith [h2, h4]

  have h6 : 2 / ((a + b) * (c + d)) = 2 / (a + b) + 2 / (c + d) := by
    have h7 : (a + b) * (c + d) = (a + b) * (c + d) := by rfl
    field_simp [(show 0 < a + b by nlinarith), (show 0 < c + d by nlinarith), (show a + b + c + d = 1 by linarith)]
    <;> nlinarith [h, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]

  linarith [h5, h6, show (a + b) * (c + d) > 0 by positivity, mul_pos ha hb, mul_pos hc hd, h1, h3]