import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_121126 {f : ℝ → ℝ} (hf : f = λ x => -3 * x ^ 2 - 5) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 2| < δ → |f x - f 2| < ε := by
  use min (1 : ℝ) (ε / 15)
  constructor
  · -- Show δ > 0
    cases' min_cases (1 : ℝ) (ε / 15) with h1 h1
    · -- Case where 1 < ε / 15
      linarith [show ε > 0 by linarith]
    · -- Case where ε / 15 ≤ 1
      linarith [show ε > 0 by linarith]
  · -- Show the implication
    intro x hx
    have h1 : f 2 = -17 := by
      rw [hf]
      norm_num
    have h2 : f x = -3 * x ^ 2 - 5 := by
      rw [hf]
    have h3 : |f x - f 2| = 3 * |x ^ 2 - 4| := by
      rw [h2, h1]
      have h4 : (-3 * x ^ 2 - 5 : ℝ) - (-17 : ℝ) = -3 * (x ^ 2 - 4) := by
        ring
      rw [h4]
      have h5 : |(-3 * (x ^ 2 - 4) : ℝ)| = 3 * |x ^ 2 - 4| := by
        have h6 : |(-3 * (x ^ 2 - 4) : ℝ)| = |(-3 : ℝ)| * |x ^ 2 - 4| := by
          apply abs_mul
        have h7 : |(-3 : ℝ)| = (3 : ℝ) := by
          norm_num
        rw [h6, h7]
      linarith [h5]
    have h4 : |x - 2| < min (1 : ℝ) (ε / 15) := hx
    cases' min_cases (1 : ℝ) (ε / 15) with h5 h5
    · -- Case where min (1 : ℝ) (ε / 15) = (1 : ℝ)
      have h4' : |x - 2| < (1 : ℝ) := by
        linarith [h4, h5]
      have h6 : x > 1 := by
        cases' abs_lt.mp h4' with h7 h8 
        linarith 
      have h7 : x < 3 := by 
        cases' abs_lt.mp h4' with h7 h8 
        linarith 
      have h10 : |x ^ 2 - 4| < (5 : ℝ) := by
        have h8 : x ^ 2 - 4 < 5 := by
          nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2)]
        have h9 : x ^ 2 - 4 > -5 := by
          nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2)]
        apply abs_lt.mpr
        constructor <;> nlinarith
      have h12 : ε ≥ (15 : ℝ) := by
        by_contra h 
        push_neg at h 
        have h5' : ε / 15 < (1 : ℝ) := by
          linarith 
        linarith [show ε / 15 ≤ (1 : ℝ) by linarith [h5]]
      have h11 : |f x - f 2| < 15 := by
        rw [h3]
        linarith 
      linarith
    · -- Case where min (1 : ℝ) (ε / 15) = ε / 15 
      have h5 : |x - 2| < ε / 15 := by 
        linarith [h4, h5]
      have h4' : |x - 2| < 1 := by
        linarith [abs_lt.mp (show |x - 2| < ε / 15 by linarith), show ε / 15 ≤ (1 : ℝ) by linarith [h5]]
      have h6 : x > 1 := by
        cases' abs_lt.mp h4' with h7 h8 
        linarith
      have h7 : x < 3 := by 
        cases' abs_lt.mp h4' with h7 h8 
        linarith 
      have h7' : |x ^ 2 - 4| < ε / 3 := by
        have h8 : x ^ 2 - 4 = (x - 2) * (x + 2) := by 
          ring
        rw [h8]
        have h50 : |(x - 2) * (x + 2)| = |x - 2| * |x + 2| := by
          rw [abs_mul]
        rw [h50]
        have h60 : |x + 2| < 5 := by
          have h5' : x < (3 : ℝ) := by
            cases' abs_lt.mp h4' with h1 h2 
            linarith 
          have h6' : x > (1 : ℝ) := by
            cases' abs_lt.mp h4' with h1 h2 
            linarith
          have h7' : x + 2 < 5 := by
            linarith 
          have h8' : x + 2 > 3 := by 
            linarith 
          apply abs_lt.mpr
          constructor <;> linarith 
        nlinarith [abs_nonneg (x - 2), abs_nonneg (x + 2), abs_nonneg (x ^ 2 - 4), h60, h5]
      rw [h3]
      linarith