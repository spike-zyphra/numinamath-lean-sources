import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_145344 (x : ℝ) (hx : 0 ≤ x) :
    8 * abs (x - sqrt x + 2) + 2 * x * sqrt x < x ^ 2 + x + 28 ↔
    x ∈ Ico 0 4 ∪ Ioi 9 := by
  constructor
  · -- Forward: If the inequality holds, prove x is in the union of intervals
    intro h
    have h1 : 0 ≤ x := hx
    have h2 : x - sqrt x + 2 ≥ 0 := by
      have h3 : sqrt x ≥ 0 := Real.sqrt_nonneg x
      nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), sq_nonneg (sqrt x - 1), Real.sqrt_nonneg x]
    have h4' : abs (x - sqrt x + 2) = x - sqrt x + 2 := by
      rw [abs_of_nonneg h2]
    have h5 : 8 * abs (x - sqrt x + 2) + 2 * x * sqrt x < x ^ 2 + x + 28 := by
      linarith [h]
    rw [h4'] at h5
    by_cases h6 : x < 4
    · -- If x < 4, then x ∈ [0; 4)
      left
      constructor
      · -- Show 0 ≤ x
        linarith
      · -- Show x < 4
        linarith
    · -- Case where x ≥ 4
      have h7 : x ≥ 4 := by linarith
      by_cases h3 : x > 9
      · -- Case where x > 9, so x ∈ (9; +∞)
        right
        exact h3
      · -- Case where 4 ≤ x ≤ 9
        have h8 : x ≤ 9 := by linarith
        exfalso
        nlinarith [sq_nonneg (x - 4), sq_nonneg (x - 9), Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), sq_nonneg ((sqrt x) - 2), sq_nonneg ((sqrt x) - 3), sq_nonneg (x - 4), sq_nonneg (x - 9), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg x)]
  · -- Backward: If x ∈ [0; 4) ∪ (9; +∞), then the inequality holds
    intro h
    rcases h with (h | h)
    · -- Case h : x ∈ [0; 4)
      rcases h with ⟨h0, h4⟩
      have h1 : 0 ≤ x := hx
      have h2 : x - sqrt x + 2 ≥ 0 := by
        have h3 : sqrt x ≥ 0 := Real.sqrt_nonneg x
        nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), sq_nonneg (sqrt x - 1), Real.sqrt_nonneg x]
      have h3' : 8 * abs (x - sqrt x + 2) + 2 * x * sqrt x < x ^ 2 + x + 28 := by
        have h4' : abs (x - sqrt x + 2) = x - sqrt x + 2 := by
          rw [abs_of_nonneg h2]
        rw [h4']
        nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), sq_nonneg (sqrt x - 2), sq_nonneg ((x) - 4), sq_nonneg ((x - 2) * (x - 4)), sq_nonneg ((sqrt x) ^ 2 - x)]
      linarith
    · -- Case h : x ∈ (9; +∞)
      have h9 : x > 9 := h
      have h1 : 0 ≤ x := hx
      have h2 : x - sqrt x + 2 ≥ 0 := by
        have h3 : sqrt x ≥ 0 := Real.sqrt_nonneg x
        nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), sq_nonneg (sqrt x - 1), Real.sqrt_nonneg x]
      have h3' : 8 * abs (x - sqrt x + 2) + 2 * x * sqrt x < x ^ 2 + x + 28 := by
        have h4' : abs (x - sqrt x + 2) = x - sqrt x + 2 := by
          rw [abs_of_nonneg h2]
        rw [h4']
        nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), sq_nonneg (sqrt x - 3), sq_nonneg (x - 9), sq_nonneg ((sqrt x) ^ 2 - x), sq_nonneg ((x - 9) * (x - 4)), sq_nonneg ((x - 4) * (sqrt x - 3))]
      linarith