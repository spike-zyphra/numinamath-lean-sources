import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_318802 (f : ℝ → ℝ) (hf : f = λ x => x^6 + 3*x^5 + 5*x^4 + 3*x^3 - 2*x^2 - 1) :
    {x | f x < 0} = {x | (x < (-1 + sqrt 5)/2 ∧ x > (-1 - sqrt 5)/2)} := by
  ext x
  simp only [hf]
  constructor
  · -- First direction: if f(x) < 0, then x is in the interval
    intro h
    have h1 : x ^ 6 + 3 * x ^ 5 + 5 * x ^ 4 + 3 * x ^ 3 - 2 * x ^ 2 - 1 < 0 := by
      simpa using h
    have h3 : x^6 + 3*x^5 + 5*x^4 + 3*x^3 - 2*x^2 - 1 = (x^2 + x - 1) * (x^4 + 2*x^3 + 4*x^2 + x + 1) := by 
      ring
    have h4 : x^2 + x - 1 = (x - (-1 + Real.sqrt 5)/2) * (x - (-1 - Real.sqrt 5)/2) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
    have h5 : x^2 + x - 1 < 0 := by
      have h6 : (x^2 + x - 1) * (x^4 + 2*x^3 + 4*x^2 + x + 1) < 0 := by 
        linarith [h1, h3]
      have h7 : x^4 + 2*x^3 + 4*x^2 + x + 1 > 0 := by
        nlinarith [sq_nonneg (x^2 + x/2), sq_nonneg (x + 1/2), sq_nonneg (x^2), sq_nonneg (x), sq_nonneg (x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      have h8 : x^2 + x - 1 < 0 := by nlinarith
      assumption
    have h6 : (x - (-1 + Real.sqrt 5)/2) * (x - (-1 - Real.sqrt 5)/2) < 0 := by
      linarith [h4, h5]
    constructor
    · -- Show x < (-1 + Real.sqrt 5)/2
      nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    · -- Show x > (-1 - Real.sqrt 5)/2
      nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  · -- Second direction: if x is in the interval, then f(x) < 0
    rintro ⟨h1, h2⟩
    have h3 : (x - (-1 + Real.sqrt 5)/2) * (x - (-1 - Real.sqrt 5)/2) < 0 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
    have h4 : x^2 + x - 1 = (x - (-1 + Real.sqrt 5)/2) * (x - (-1 - Real.sqrt 5)/2) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
    have h7 : x^2 + x - 1 < 0 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
    have h8 : x^4 + 2*x^3 + 4*x^2 + x + 1 > 0 := by
      nlinarith [sq_nonneg (x^2 + x/2), sq_nonneg (x + 1/2), sq_nonneg (x^2), sq_nonneg (x), sq_nonneg (x + 1), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num)]
    have h9 : (x^2 + x - 1) * (x^4 + 2*x^3 + 4*x^2 + x + 1) < 0 := by 
      nlinarith
    have h10 : x^6 + 3*x^5 + 5*x^4 + 3*x^3 - 2*x^2 - 1 < 0 := by
      nlinarith
    simpa using h10