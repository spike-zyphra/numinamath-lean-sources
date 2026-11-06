import Mathlib

open Real

theorem inequalities_277135 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (sqrt a + sqrt b)^8 ≥ 64 * a * b * (a + b)^2 := by
  have h1 : 0 ≤ a := by linarith
  have h2 : 0 ≤ b := by linarith
  have h3 : sqrt a ≥ 0 := Real.sqrt_nonneg a
  have h4 : sqrt b ≥ 0 := Real.sqrt_nonneg b
  have h5 : sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  have h6 : sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have h7 : (sqrt a + sqrt b) ^ 2 = a + b + 2 * (sqrt a * sqrt b) := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), h5, h6, mul_nonneg (show 0 ≤ (a : ℝ) by linarith) (show 0 ≤ (b : ℝ) by linarith), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  have h18 : (a + b + 2 * (sqrt a * sqrt b)) ^ 2 ≥ 8 * (sqrt a * sqrt b) * (a + b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (sqrt a ^ 2 - sqrt b ^ 2), sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a * sqrt b - a / 2), sq_nonneg (sqrt a * sqrt b - b / 2), sq_nonneg (a + b - 2 * sqrt a * sqrt b), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), Real.mul_self_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.mul_self_sqrt (show 0 ≤ (b : ℝ) by linarith), mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), sq_nonneg (sqrt a ^ 2 - sqrt b ^ 2), sq_nonneg ((sqrt a + sqrt b) ^ 2 - 4 * (sqrt a * sqrt b)), sq_nonneg (sqrt a - sqrt b)]
  have h19 : ((a + b + 2 * (sqrt a * sqrt b)) ^ 2) ^ 2 ≥ 64 * a * b * (a + b) ^ 2 := by
    have h20 : (a + b + 2 * (sqrt a * sqrt b)) ^ 2 ≥ 8 * (sqrt a * sqrt b) * (a + b) := h18
    have h21 : ((a + b + 2 * (sqrt a * sqrt b)) ^ 2) ^ 2 ≥ (8 * (sqrt a * sqrt b) * (a + b)) ^ 2 := by
      have h30 : (a + b + 2 * (sqrt a * sqrt b)) ^ 2 ≥ 0 := by nlinarith
      have h31 : (8 * (sqrt a * sqrt b) * (a + b)) ≥ 0 := by
        positivity
      have h32 : (a + b + 2 * (sqrt a * sqrt b)) ^ 2 ≥ (8 * (sqrt a * sqrt b) * (a + b)) := h18
      nlinarith [sq_nonneg ((a + b + 2 * (sqrt a * sqrt b)) ^ 2 - (8 * (sqrt a * sqrt b) * (a + b)))]
    have h23 : (8 * (sqrt a * sqrt b) * (a + b)) ^ 2 = 64 * a * b * (a + b) ^ 2 := by
      have h24 : (sqrt a * sqrt b) = Real.sqrt a * Real.sqrt b := by rfl
      calc
        (8 * (sqrt a * sqrt b) * (a + b)) ^ 2 = 64 * ((sqrt a * sqrt b) ^ 2) * (a + b) ^ 2 := by ring
        _ = 64 * (a * b) * (a + b) ^ 2 := by
          have h10 : (sqrt a * sqrt b) ^ 2 = a * b := by
            calc
              (sqrt a * sqrt b) ^ 2 = (sqrt a) ^ 2 * (sqrt b) ^ 2 := by ring
              _ = a * b := by
                rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
          rw [h10]
        _ = 64 * a * b * (a + b) ^ 2 := by ring
    nlinarith [h21, h23]
  have h24 : (sqrt a + sqrt b) ^ 8 = ((a + b + 2 * (sqrt a * sqrt b)) ^ 2) ^ 2 := by
    calc
      (sqrt a + sqrt b) ^ 8 = ((sqrt a + sqrt b) ^ 4) ^ 2 := by ring
      _ = ((a + b + 2 * (sqrt a * sqrt b)) ^ 2) ^ 2 := by
        have h14 : (sqrt a + sqrt b) ^ 4 = (a + b + 2 * (sqrt a * sqrt b)) ^ 2 := by
          calc
            (sqrt a + sqrt b) ^ 4 = ((sqrt a + sqrt b) ^ 2) ^ 2 := by ring
            _ = (a + b + 2 * (sqrt a * sqrt b)) ^ 2 := by
              rw [h7]
        rw [h14]
  nlinarith [h24, h19]