import Mathlib
theorem algebra_605787 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    √((a ^ 2 + a * b + b ^ 2) / 3) + √(a * b) ≤ a + b := by
  have h1 : 0 ≤ (a ^ 2 + a * b + b ^ 2) / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b, mul_pos ha hb]
  have h2 : 0 ≤ a * b := by
    nlinarith [mul_pos ha hb]
  have h3 : √((a ^ 2 + a * b + b ^ 2) / 3) ≥ 0 := by positivity
  have h4 : √(a * b) ≥ 0 := by positivity
  have h5 : (√((a ^ 2 + a * b + b ^ 2) / 3) + √(a * b)) ^ 2 ≤ (a + b) ^ 2 := by
    have h6 : (√((a ^ 2 + a * b + b ^ 2) / 3) + √(a * b)) ^ 2 =
        (√((a ^ 2 + a * b + b ^ 2) / 3)) ^ 2 + (√(a * b)) ^ 2 + 2 * (√((a ^ 2 + a * b + b ^ 2) / 3) * √(a * b)) := by ring
    have h7 : (√((a ^ 2 + a * b + b ^ 2) / 3)) ^ 2 = (a ^ 2 + a * b + b ^ 2) / 3 := by
      rw [Real.sq_sqrt]
      linarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b, mul_pos ha hb]
    have h8 : (√(a * b)) ^ 2 = a * b := by
      rw [Real.sq_sqrt]
      nlinarith [mul_pos ha hb]
    have h9 : (√((a ^ 2 + a * b + b ^ 2) / 3) * √(a * b)) = Real.sqrt (( (a ^ 2 + a * b + b ^ 2) / 3 ) * (a * b)) := by
      rw [← Real.sqrt_mul (by
        nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b, mul_pos ha hb]
      )]
    rw [h6]
    rw [h7, h8, h9]
    have h10 : (a ^ 2 + a * b + b ^ 2) / 3 + a * b + 2 * Real.sqrt (( (a ^ 2 + a * b + b ^ 2) / 3 ) * (a * b)) ≤ (a + b) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (( (a ^ 2 + a * b + b ^ 2) / 3 ) * (a * b) ), sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a + b - 2 * Real.sqrt (( (a ^ 2 + a * b + b ^ 2) / 3 ) * (a * b))), sq_nonneg (Real.sqrt (( (a ^ 2 + a * b + b ^ 2) / 3 ) * (a * b)) ), Real.sq_sqrt (show (0 : ℝ) ≤ ( (a ^ 2 + a * b + b ^ 2) / 3 ) * (a * b) by nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b, mul_pos ha hb] ) ]
    linarith
  have h6 : √((a ^ 2 + a * b + b ^ 2) / 3) + √(a * b) ≤ a + b := by
    nlinarith [Real.sqrt_nonneg ((a ^ 2 + a * b + b ^ 2) / 3), Real.sqrt_nonneg (a * b), h5, mul_pos ha hb]
  exact h6