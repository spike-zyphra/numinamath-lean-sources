import Mathlib

theorem inequalities_45274 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) + Real.sqrt (a * b) ≤ a + b := by
  have h1 : 0 ≤ Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have h3 : Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) ≥ 0 := Real.sqrt_nonneg ((a ^ 2 + a * b + b ^ 2) / 3)
  have h4 : Real.sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
  have h5 : (Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) + Real.sqrt (a * b)) ^ 2 ≤ (a + b) ^ 2 := by
    have h6 : (Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) + Real.sqrt (a * b)) ^ 2 =
        Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) ^ 2 + Real.sqrt (a * b) ^ 2 + 2 * (Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) * Real.sqrt (a * b)) := by
      ring
    rw [h6]
    have h7 : Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) ^ 2 = (a ^ 2 + a * b + b ^ 2) / 3 := Real.sq_sqrt (by positivity)
    have h8 : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (by positivity)
    rw [h7, h8]
    nlinarith [sq_nonneg (Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) - Real.sqrt (a * b)), sq_nonneg (a - b), mul_nonneg (Real.sqrt_nonneg ((a ^ 2 + a * b + b ^ 2) / 3)) (Real.sqrt_nonneg (a * b)), sq_nonneg (a - b)]
  nlinarith [Real.sqrt_nonneg ((a ^ 2 + a * b + b ^ 2) / 3), Real.sqrt_nonneg (a * b), sq_nonneg (Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) - Real.sqrt (a * b)), sq_nonneg (a - b), Real.sq_sqrt (show 0 ≤ (a ^ 2 + a * b + b ^ 2) / 3 by positivity), Real.sq_sqrt (show 0 ≤ a * b by positivity), mul_nonneg (Real.sqrt_nonneg ((a ^ 2 + a * b + b ^ 2) / 3)) (Real.sqrt_nonneg (a * b))]