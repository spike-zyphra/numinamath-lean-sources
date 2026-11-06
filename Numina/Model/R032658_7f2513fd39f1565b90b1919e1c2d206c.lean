import Mathlib

open Real

theorem inequalities_39361 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    sqrt (a ^ 4 + c ^ 4) + sqrt (a ^ 4 + d ^ 4) + sqrt (b ^ 4 + c ^ 4) + sqrt (b ^ 4 + d ^ 4) ≥
    2 * sqrt 2 * (a * d + b * c) := by

  have h1 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : sqrt (x ^ 4 + y ^ 4) ≥ Real.sqrt 2 / 2 * (x ^ 2 + y ^ 2) := by
    have h2 : (x ^ 4 + y ^ 4 : ℝ) ≥ ( (x ^ 2 + y ^ 2) ^ 2 / 2 ) := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
    have h3 : sqrt (x ^ 4 + y ^ 4) ≥ sqrt ( (x ^ 2 + y ^ 2) ^ 2 / 2 ) := Real.sqrt_le_sqrt (by linarith)
    have h4 : sqrt ( (x ^ 2 + y ^ 2) ^ 2 / 2 ) = (x ^ 2 + y ^ 2) / Real.sqrt 2 := by
      have h5 : ( (x ^ 2 + y ^ 2) ^ 2 / 2 : ℝ ) = ( (x ^ 2 + y ^ 2) / Real.sqrt 2 ) ^ 2 := by
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
      rw [h5]
      rw [Real.sqrt_sq_eq_abs]
      have h6 : 0 ≤ (x ^ 2 + y ^ 2 : ℝ) / Real.sqrt 2 := by
        apply div_nonneg
        nlinarith [sq_nonneg x, sq_nonneg y]
        positivity
      rw [abs_of_nonneg h6]
    have h7 : (x ^ 2 + y ^ 2) / Real.sqrt 2 = Real.sqrt 2 / 2 * (x ^ 2 + y ^ 2) := by
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    linarith [h7, h4, h3]

  have h2 := h1 ha hc
  have h3 := h1 ha hd
  have h4 := h1 hb hc
  have h5 := h1 hb hd
  have h6 : sqrt (a ^ 4 + c ^ 4) + sqrt (a ^ 4 + d ^ 4) + sqrt (b ^ 4 + c ^ 4) + sqrt (b ^ 4 + d ^ 4) ≥ 
      Real.sqrt 2 / 2 * (a ^ 2 + c ^ 2) + Real.sqrt 2 / 2 * (a ^ 2 + d ^ 2) + Real.sqrt 2 / 2 * (b ^ 2 + c ^ 2) + Real.sqrt 2 / 2 * (b ^ 2 + d ^ 2) := by 
    linarith [h2, h3, h4, h5]

  have h7 : Real.sqrt 2 / 2 * (a ^ 2 + c ^ 2) + Real.sqrt 2 / 2 * (a ^ 2 + d ^ 2) + Real.sqrt 2 / 2 * (b ^ 2 + c ^ 2) + Real.sqrt 2 / 2 * (b ^ 2 + d ^ 2) = Real.sqrt 2 * (a^2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    ring_nf

  have h8 : Real.sqrt 2 * (a^2 + b ^ 2 + c ^ 2 + d ^ 2) ≥ 2 * Real.sqrt 2 * (a * d + b * c) := by
    have h9 : a^2 + b^2 + c^2 + d^2 ≥ 2 * (a * d + b * c) := by
      nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
    have h10 : Real.sqrt 2 * (a^2 + b ^ 2 + c ^ 2 + d ^ 2) ≥ Real.sqrt 2 * (2 * (a * d + b * c)) := by
      apply mul_le_mul_of_nonneg_left
      linarith [h9]
      positivity
    linarith [h10]

  linarith [h6, h7, h8]