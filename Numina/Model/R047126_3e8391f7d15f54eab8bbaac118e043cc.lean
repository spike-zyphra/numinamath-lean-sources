import Mathlib

open Real

theorem inequalities_199271 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (sqrt a + sqrt b)^8 ≥ 64 * a * b * (a + b)^2 := by
  have h1 : 0 ≤ sqrt a := Real.sqrt_nonneg a
  have h2 : 0 ≤ sqrt b := Real.sqrt_nonneg b
  have h3 : (sqrt a + sqrt b) ^ 4 ≥ 8 * (sqrt a * sqrt b) * (a + b) := by
    have h4 : (sqrt a + sqrt b) ^ 4 - 8 * (sqrt a * sqrt b) * (a + b) ≥ 0 := by
      have h5 : (sqrt a + sqrt b) ^ 4 - 8 * (sqrt a * sqrt b) * (a + b) = (sqrt a - sqrt b) ^ 4 := by
        have h6 : (sqrt a + sqrt b) ^ 4 = (sqrt a) ^ 4 + 4 * (sqrt a) ^ 3 * (sqrt b) + 6 * (sqrt a) ^ 2 * (sqrt b) ^ 2 + 4 * (sqrt a) * (sqrt b) ^ 3 + (sqrt b) ^ 4 := by
          ring_nf
        have h7 : (sqrt a - sqrt b) ^ 4 = (sqrt a) ^ 4 - 4 * (sqrt a) ^ 3 * (sqrt b) + 6 * (sqrt a) ^ 2 * (sqrt b) ^ 2 - 4 * (sqrt a) * (sqrt b) ^ 3 + (sqrt b) ^ 4 := by
          ring_nf
        have h8 : (sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
        have h9 : (sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
        nlinarith [sq_nonneg (sqrt a ^ 2 - sqrt b ^ 2), sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a + sqrt b),
          Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
      have h12 : (sqrt a - sqrt b) ^ 4 ≥ 0 := by positivity
      linarith
    linarith
  have h4 : ((sqrt a + sqrt b) ^ 4) ^ 2 ≥ (8 * (sqrt a * sqrt b) * (a + b)) ^ 2 := by
    have h7 : (sqrt a + sqrt b) ^ 4 ≥ (8 * (sqrt a * sqrt b) * (a + b)) := h3
    have h8 : (sqrt a + sqrt b) ^ 4 ≥ 0 := by positivity
    have h9 : (8 * (sqrt a * sqrt b) * (a + b)) ≥ 0 := by positivity
    nlinarith [sq_nonneg ((sqrt a + sqrt b) ^ 4 - (8 * (sqrt a * sqrt b) * (a + b))), sq_nonneg ((sqrt a + sqrt b) ^ 4), sq_nonneg ((8 * (sqrt a * sqrt b) * (a + b)))]
  have h5 : ((sqrt a + sqrt b) ^ 4) ^ 2 = (sqrt a + sqrt b) ^ 8 := by ring
  have h6 : (8 * (sqrt a * sqrt b) * (a + b)) ^ 2 = 64 * a * b * (a + b) ^ 2 := by
    have h10 : (sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
    have h11 : (sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
    calc
      (8 * (sqrt a * sqrt b) * (a + b)) ^ 2
          = 64 * ((sqrt a * sqrt b) ^ 2) * ((a + b) ^ 2) := by ring
      _ = 64 * ((sqrt a) ^ 2 * (sqrt b) ^ 2) * ((a + b) ^ 2) := by ring
      _ = 64 * (a * b) * ((a + b) ^ 2) := by
        rw [show (sqrt a) ^ 2 = a by linarith, show (sqrt b) ^ 2 = b by linarith]
      _ = 64 * a * b * (a + b) ^ 2 := by ring
  linarith [h4, h5, h6]