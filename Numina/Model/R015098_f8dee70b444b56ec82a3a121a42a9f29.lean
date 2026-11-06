import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_598409 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b + 4 * c ^ 2 = 1) :
  sqrt a + sqrt b + sqrt 2 * c ≤ sqrt 10 / 2 := by
  have h1 : 0 ≤ a := by linarith
  have h2 : 0 ≤ b := by linarith
  have h3 : 0 ≤ c := by linarith
  have h4 : (sqrt a + sqrt b + sqrt 2 * c) ^ 2 ≤ 10 / 4 := by
    have h12 : a + b = 1 - 4 * c ^ 2 := by linarith
    have h14 : (sqrt 2 * c) ^ 2 = 2 * c ^ 2 := by 
      calc
        (sqrt 2 * c) ^ 2 = (sqrt 2) ^ 2 * c ^ 2 := by ring
        _ = 2 * c ^ 2 := by rw [Real.sq_sqrt]; positivity
    nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (c ^ 2 - 1 / 20), sq_nonneg (sqrt a + sqrt b - 2 * Real.sqrt (2 / 5)), sq_nonneg (c - Real.sqrt (1 / 20)), 
          Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (10 : ℝ), 
          Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (c ^ 2)), 
          Real.sq_sqrt (show 0 ≤ (c ^ 2 : ℝ) by positivity), 
          mul_nonneg (show (0 : ℝ) ≤ (c) by linarith) (show (0 : ℝ) ≤ (c) by linarith)]
  have h7 : sqrt a + sqrt b + sqrt 2 * c ≤ Real.sqrt (10 / 4) := by
    have h8 : (sqrt a + sqrt b + sqrt 2 * c) ^ 2 ≤ (10 / 4 : ℝ) := h4
    have h9 : sqrt a + sqrt b + sqrt 2 * c ≥ 0 := by
      positivity
    have h10 : Real.sqrt ((sqrt a + sqrt b + sqrt 2 * c) ^ 2) ≤ Real.sqrt (10 / 4) := Real.sqrt_le_sqrt (h8)
    have h11 : Real.sqrt ((sqrt a + sqrt b + sqrt 2 * c) ^ 2) = sqrt a + sqrt b + sqrt 2 * c := by
      rw [Real.sqrt_sq (show 0 ≤ sqrt a + sqrt b + sqrt 2 * c by positivity)]
    linarith
  have h8 : Real.sqrt (10 / 4) = Real.sqrt 10 / 2 := by
    have h9 : Real.sqrt (10 / 4) = Real.sqrt 10 / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    linarith
  linarith [h7, h8]