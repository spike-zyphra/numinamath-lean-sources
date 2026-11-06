import Mathlib

open Real
open scoped BigOperators

theorem inequalities_31448 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  (-a + b + c) * (a - b + c) + (a - b + c) * (a + b - c) +
  (a + b - c) * (-a + b + c) ≤
  sqrt (a * b * c) * (sqrt a + sqrt b + sqrt c) := by
    have h1 : 0 ≤ sqrt a := Real.sqrt_nonneg a
    have h2 : 0 ≤ sqrt b := Real.sqrt_nonneg b
    have h3 : 0 ≤ sqrt c := Real.sqrt_nonneg c
    have h4 : (sqrt a) ^ 2 = a := Real.sq_sqrt (show 0 ≤ a by linarith)
    have h5 : (sqrt b) ^ 2 = b := Real.sq_sqrt (show 0 ≤ b by linarith)
    have h6 : (sqrt c) ^ 2 = c := Real.sq_sqrt (show 0 ≤ c by linarith)
    have h7 : sqrt (a * b * c) = sqrt a * sqrt b * sqrt c := by
      have h8 : sqrt (a * b * c) = sqrt ((a * b) * c) := by ring_nf
      have h9 : sqrt ((a * b) * c) = sqrt (a * b) * sqrt c := by
        rw [Real.sqrt_mul]
        positivity
      have h10 : sqrt (a * b) = sqrt a * sqrt b := by
        rw [Real.sqrt_mul]
        positivity
      rw [h8, h9, h10]
      all_goals positivity
    nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt b - sqrt c), sq_nonneg (sqrt c - sqrt a),
      Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith),
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c),
      h, h', h'']