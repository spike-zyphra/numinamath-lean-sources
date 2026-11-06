import Mathlib

open Real
open scoped BigOperators

theorem inequalities_70443 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  (a + b) * sqrt (a * b) + (a + c) * sqrt (a * c) + (b + c) * sqrt (b * c) ≥
  (a + b + c)^2 / 2 := by
  have hab1 : 0 ≤ a * b := by positivity
  have hab : sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have hac1 : 0 ≤ a * c := by positivity
  have hac : sqrt (a * c) = Real.sqrt a * Real.sqrt c := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have hbc1 : 0 ≤ b * c := by positivity
  have hbc : sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  rw [hab, hac, hbc]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a - Real.sqrt c), sq_nonneg (Real.sqrt b - Real.sqrt c),
    sq_nonneg (Real.sqrt a * Real.sqrt b - Real.sqrt a * Real.sqrt c), sq_nonneg (Real.sqrt a * Real.sqrt b - Real.sqrt b * Real.sqrt c), sq_nonneg (Real.sqrt a * Real.sqrt c - Real.sqrt b * Real.sqrt c),
    Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c), 
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c),
    sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
    Real.sq_sqrt (show (0 : ℝ) ≤ a by positivity), 
    Real.sq_sqrt (show (0 : ℝ) ≤ b by positivity), 
    Real.sq_sqrt (show (0 : ℝ) ≤ c by positivity),
    mul_nonneg (show (0 : ℝ) ≤ Real.sqrt a by positivity) (show (0 : ℝ) ≤ Real.sqrt b by positivity), 
    mul_nonneg (show (0 : ℝ) ≤ Real.sqrt a by positivity) (show (0 : ℝ) ≤ Real.sqrt c by positivity), 
    mul_nonneg (show (0 : ℝ) ≤ Real.sqrt b by positivity) (show (0 : ℝ) ≤ Real.sqrt c by positivity)
  ]