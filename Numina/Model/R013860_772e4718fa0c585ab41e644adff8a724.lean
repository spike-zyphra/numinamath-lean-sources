import Mathlib

open Real
open scoped BigOperators

theorem inequalities_597203 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + C ≤ 2 * B)
  (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (h : a = b * sin A / sin B) (h' : c = b * sin C / sin B) :
  a ^ (1 / 2) + c ^ (1 / 2) ≤ 2 * b ^ (1 / 2) ∧
  a ^ (1 / 3) + c ^ (1 / 3) ≤ 2 * b ^ (1 / 3) ∧
  a ^ (1 / 4) + c ^ (1 / 4) ≤ 2 * b ^ (1 / 4) := by
  constructor
  · -- Proof for n = 1/2
    have h11 : 0 < b := by linarith
    have h12 : 0 < a := by linarith
    have h13 : 0 < c := by linarith
    have h111 : a ^ (1 / 2) ≥ 0 := by positivity
    have h112 : c ^ (1 / 2) ≥ 0 := by positivity
    have h113 : b ^ (1 / 2) ≥ 0 := by positivity
    nlinarith [sq_nonneg (a ^ (1 / 2) - c ^ (1 / 2)), 
      sq_nonneg (a ^ (1 / 2) - b ^ (1 / 2)), 
      sq_nonneg (c ^ (1 / 2) - b ^ (1 / 2)),
      Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith),
      hABC, 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c)
    ]
  constructor
  · -- Proof for n = 1/3
    have h11 : 0 < b := by linarith
    have h12 : 0 < a := by linarith
    have h13 : 0 < c := by linarith
    have h111 : a ^ (1 / 3) ≥ 0 := by positivity
    have h112 : c ^ (1 / 3) ≥ 0 := by positivity
    have h113 : b ^ (1 / 3) ≥ 0 := by positivity
    nlinarith [sq_nonneg (a ^ (1 / 3) - c ^ (1 / 3)), 
      sq_nonneg (a ^ (1 / 3) - b ^ (1 / 3)), 
      sq_nonneg (c ^ (1 / 3) - b ^ (1 / 3)), 
      Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith),
      hABC, 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c)
    ]
  · -- Proof for n = 1/4
    have h11 : 0 < b := by linarith
    have h12 : 0 < a := by linarith
    have h13 : 0 < c := by linarith
    have h111 : a ^ (1 / 4) ≥ 0 := by positivity
    have h112 : c ^ (1 / 4) ≥ 0 := by positivity
    have h113 : b ^ (1 / 4) ≥ 0 := by positivity
    nlinarith [sq_nonneg (a ^ (1 / 4) - c ^ (1 / 4)), 
      sq_nonneg (a ^ (1 / 4) - b ^ (1 / 4)), 
      sq_nonneg (c ^ (1 / 4) - b ^ (1 / 4)), 
      Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith),
      hABC, 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c)
    ]