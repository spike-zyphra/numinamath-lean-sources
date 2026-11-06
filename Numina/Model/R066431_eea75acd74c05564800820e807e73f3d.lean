import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_112267 (x : ℝ) (hx : 0 ≤ 2 - x) :
    x^2 + sqrt (2 - x) ≤ 2 ↔ (x ≥ (1 - sqrt 5) / 2 ∧ x ≤ 1) := by
  constructor
  · -- Forward implication: If x^2 + sqrt(2-x) ≤ 2, then (x ≥ (1 - sqrt 5) / 2 ∧ x ≤ 1)
    intro h
    have h1 : x ≤ 1 := by 
      nlinarith [Real.sqrt_nonneg (2 - x), Real.sq_sqrt (show (0 : ℝ) ≤ 2 - x by linarith), h, sq_nonneg (x - 1)]
    
    have h2 : x ≥ (1 - Real.sqrt 5) / 2 := by
      nlinarith [Real.sqrt_nonneg (2 - x), Real.sq_sqrt (show (0 : ℝ) ≤ 2 - x by linarith), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), sq_nonneg (x - (1 - Real.sqrt 5) / 2), sq_nonneg (x - 1), sq_nonneg (sqrt (2 - x) - 1), sq_nonneg (sqrt (2 - x) - (1 + Real.sqrt 5) / 2)]
    
    constructor <;> linarith

  · -- Reverse implication: If (x ≥ (1 - sqrt 5) / 2 ∧ x ≤ 1), then x^2 + sqrt (2 - x) ≤ 2
    rintro ⟨h1, h2⟩
    have h3 : 0 ≤ (2 : ℝ) - x := by linarith
    have h4 : sqrt (2 - x) ≥ 0 := Real.sqrt_nonneg (2 - x)
    
    nlinarith [Real.sqrt_nonneg (2 - x), Real.sq_sqrt (show (0 : ℝ) ≤ 2 - x by linarith), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h1, h2, sq_nonneg (sqrt (2 - x) - 1), sq_nonneg (sqrt (2 - x) - (1 + Real.sqrt 5) / 2), sq_nonneg (x - 1), sq_nonneg (x - (1 - Real.sqrt 5) / 2)]