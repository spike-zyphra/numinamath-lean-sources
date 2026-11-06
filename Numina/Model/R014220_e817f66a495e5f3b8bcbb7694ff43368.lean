import Mathlib

theorem inequalities_189894 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt a + Real.sqrt (a + 3 * b) < Real.sqrt (a + b) + Real.sqrt (a + 2 * b) := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < a + 3 * b := by
    nlinarith
  have h4 : 0 < a + b := by
    nlinarith
  have h5 : 0 < a + 2 * b := by
    nlinarith
  have h6 : (Real.sqrt a + Real.sqrt (a + 3 * b)) ^ 2 < (Real.sqrt (a + b) + Real.sqrt (a + 2 * b)) ^ 2 := by
    have h7 : (Real.sqrt a + Real.sqrt (a + 3 * b)) ^ 2 =
        (Real.sqrt a) ^ 2 + (Real.sqrt (a + 3 * b)) ^ 2 + 2 * (Real.sqrt a * Real.sqrt (a + 3 * b)) := by ring
    have h8 : (Real.sqrt (a + b) + Real.sqrt (a + 2 * b)) ^ 2 =
        (Real.sqrt (a + b)) ^ 2 + (Real.sqrt (a + 2 * b)) ^ 2 + 2 * (Real.sqrt (a + b) * Real.sqrt (a + 2 * b)) := by ring
    rw [h7, h8]
    have h9 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
    have h10 : (Real.sqrt (a + 3 * b)) ^ 2 = a + 3 * b := Real.sq_sqrt (by linarith)
    have h11 : (Real.sqrt (a + b)) ^ 2 = a + b := Real.sq_sqrt (by linarith)
    have h12 : (Real.sqrt (a + 2 * b)) ^ 2 = a + 2 * b := Real.sq_sqrt (by linarith)
    rw [h9, h10, h11, h12]
    have h16 : a * (a + 3 * b) < (a + b) * (a + 2 * b) := by
      nlinarith [mul_pos ha hb]
    have h17 : Real.sqrt (a * (a + 3 * b)) < Real.sqrt ((a + b) * (a + 2 * b)) := by
      apply Real.sqrt_lt_sqrt
      nlinarith [mul_pos ha hb]
      nlinarith [mul_pos ha hb, h16]
    have h18 : Real.sqrt a * Real.sqrt (a + 3 * b) < Real.sqrt (a + b) * Real.sqrt (a + 2 * b) := by
      have h19 : Real.sqrt a * Real.sqrt (a + 3 * b) = Real.sqrt (a * (a + 3 * b)) := by
        rw [← Real.sqrt_mul (by nlinarith)]
      have h20 : Real.sqrt (a + b) * Real.sqrt (a + 2 * b) = Real.sqrt ((a + b) * (a + 2 * b)) := by
        rw [← Real.sqrt_mul (by nlinarith)]
      rw [h19, h20]
      linarith [h17]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg (a + 3 * b), Real.sqrt_nonneg (a + b), Real.sqrt_nonneg (a + 2 * b), Real.sqrt_nonneg (a * (a + 3 * b)), Real.sqrt_nonneg ((a + b) * (a + 2 * b)), Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (a + 3 * b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (a + b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (a + 2 * b : ℝ) by linarith), h18]
  have h7 : 0 ≤ Real.sqrt a + Real.sqrt (a + 3 * b) := by
    positivity
  have h8 : 0 ≤ Real.sqrt (a + b) + Real.sqrt (a + 2 * b) := by
    positivity
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg (a + 3 * b), Real.sqrt_nonneg (a + b), Real.sqrt_nonneg (a + 2 * b), h6]