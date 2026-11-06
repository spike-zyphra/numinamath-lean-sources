import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_327937 (f : ℝ → ℝ) (a : ℝ)
  (hf : f = λ x => abs (8 * x ^ 3 - 12 * x - a) + a)
  (hmax : ∃ x ∈ Icc 0 1, f x = 0)
  (ha : ∀ x ∈ Icc 0 1, f x ≤ 0) :
  a ≤ -2 * sqrt 2 := by

  have h1 := ha (Real.sqrt 2 / 2) (by
    constructor
    · -- Show that sqrt(2)/2 ≥ 0
      have h1 : 0 ≤ Real.sqrt 2 / 2 := by
        have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      linarith
    · -- Show that sqrt(2)/2 ≤ 1
      have h2 : Real.sqrt 2 / 2 ≤ 1 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
      linarith
  )

  have h2 : f (Real.sqrt 2 / 2) = abs (8 * (Real.sqrt 2 / 2) ^ 3 - 12 * (Real.sqrt 2 / 2) - a) + a := by 
    rw [hf]

  have h3 : (8 * (Real.sqrt 2 / 2) ^ 3 - 12 * (Real.sqrt 2 / 2) : ℝ) = -4 * Real.sqrt 2 := by
    have h4 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    have h5 : (Real.sqrt 2) ^ 3 = Real.sqrt 2 * 2 := by
      calc
        (Real.sqrt 2) ^ 3 = (Real.sqrt 2) * (Real.sqrt 2) ^ 2 := by ring
        _ = (Real.sqrt 2) * 2 := by rw [h4]
        _ = Real.sqrt 2 * 2 := by ring
    nlinarith [h5]

  rw [h2] at h1
  rw [h3] at h1

  cases' abs_cases (-4 * Real.sqrt 2 - a) with h4 h4 <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), sq_nonneg a]