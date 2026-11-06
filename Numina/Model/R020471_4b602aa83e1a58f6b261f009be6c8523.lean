import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11050 {x : ℝ} (hx : x ≥ 2010) :
    sqrt (x - 2009 - 2 * sqrt (x - 2010)) +
    sqrt (x - 2009 + 2 * sqrt (x - 2010)) = 2 ↔
    2010 ≤ x ∧ x ≤ 2011 := by
  constructor
  · -- Assume the equation hold, show 2010 ≤ x ∧ x ≤ 2011
    intro h
    have h1 : x - 2010 ≥ 0 := by linarith
    have h2 : sqrt (x - 2010) ≥ 0 := Real.sqrt_nonneg (x - 2010)
    have h3 : sqrt (x - 2010) ^ 2 = x - 2010 := by
      calc
        sqrt (x - 2010) ^ 2 = (Real.sqrt (x - 2010)) ^ 2 := by ring_nf
        _ = x - 2010 := Real.sq_sqrt (by linarith)
    have h4 : x - 2009 - 2 * sqrt (x - 2010) = (sqrt (x - 2010) - 1) ^ 2 := by
      nlinarith [h2, h3]
    have h5 : x - 2009 + 2 * sqrt (x - 2010) = (sqrt (x - 2010) + 1) ^ 2 := by
      nlinarith [h2, h3]
    have h6 : sqrt (x - 2009 - 2 * sqrt (x - 2010)) = |sqrt (x - 2010) - 1| := by
      rw [h4]
      have : sqrt ((sqrt (x - 2010) - 1) ^ 2) = |sqrt (x - 2010) - 1| := by
        rw [Real.sqrt_sq_eq_abs]
      exact this
    have h7 : sqrt (x - 2009 + 2 * sqrt (x - 2010)) = sqrt (x - 2010) + 1 := by
      rw [h5]
      have h8 : sqrt ((sqrt (x - 2010) + 1) ^ 2) = sqrt (x - 2010) + 1 := by
        rw [Real.sqrt_sq (show 0 ≤ (sqrt (x - 2010) + 1 : ℝ) by positivity)]
        all_goals nlinarith
      nlinarith [h8]
    rw [h6, h7] at h
    cases' abs_cases (sqrt (x - 2010) - 1) with h8 h8
    · -- sqrt (x - 2010) - 1 ≥ 0
      constructor
      · -- 2010 ≤ x
        nlinarith [h2, h3, h8]
      · -- x ≤ 2011
        nlinarith [h2, h3, h8]
    · -- sqrt (x - 2010) - 1 < 0
      constructor
      · -- 2010 ≤ x
        nlinarith [h2, h3, h8]
      · -- x ≤ 2011
        nlinarith [h2, h3, h8]
  · -- Assume 2010 ≤ x ∧ x ≤ 2011, show the equation holds
    rintro ⟨hx1, hx2⟩
    have h1 : x - 2010 ≥ 0 := by linarith
    have h2 : sqrt (x - 2010) ≥ 0 := Real.sqrt_nonneg (x - 2010)
    have h3 : sqrt (x - 2010) ^ 2 = x - 2010 := by
      calc
        sqrt (x - 2010) ^ 2 = (Real.sqrt (x - 2010)) ^ 2 := by ring_nf
        _ = x - 2010 := Real.sq_sqrt (by linarith)
    have h4 : x - 2009 - 2 * sqrt (x - 2010) = (sqrt (x - 2010) - 1) ^ 2 := by
      nlinarith [h2, h3]
    have h5 : x - 2009 + 2 * sqrt (x - 2010) = (sqrt (x - 2010) + 1) ^ 2 := by
      nlinarith [h2, h3]
    have h6 : sqrt (x - 2009 - 2 * sqrt (x - 2010)) = |sqrt (x - 2010) - 1| := by
      rw [h4]
      have : sqrt ((sqrt (x - 2010) - 1) ^ 2) = |sqrt (x - 2010) - 1| := by
        rw [Real.sqrt_sq_eq_abs]
      exact this
    have h7 : sqrt (x - 2009 + 2 * sqrt (x - 2010)) = sqrt (x - 2010) + 1 := by
      rw [h5]
      have h8 : sqrt ((sqrt (x - 2010) + 1) ^ 2) = sqrt (x - 2010) + 1 := by
        rw [Real.sqrt_sq (show 0 ≤ (sqrt (x - 2010) + 1 : ℝ) by positivity)]
        all_goals nlinarith
      nlinarith [h8]
    rw [h6, h7]
    have h8 : sqrt (x - 2010) ≤ 1 := by
      nlinarith [Real.sqrt_nonneg (x - 2010), Real.sq_sqrt (show (0: ℝ) ≤ x - 2010 by linarith)]
    cases' abs_cases (sqrt (x - 2010) - 1) with h9 h9
    · -- sqrt (x - 2010) - 1 ≥ 0
      nlinarith [Real.sqrt_nonneg (x - 2010), Real.sq_sqrt (show (0: ℝ) ≤ x - 2010 by linarith)]
    · -- sqrt (x - 2010) - 1 < 0
      nlinarith [Real.sqrt_nonneg (x - 2010), Real.sq_sqrt (show (0: ℝ) ≤ x - 2010 by linarith)]