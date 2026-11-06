import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_127374
  (f : ℝ → ℝ)
  (ε : ℝ)
  (h₀ : f = λ x => -5 * x ^ 2 - 7)
  (h₁ : ε > 0) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 1| < δ → |f x - f 1| < ε := by 
  use min (1 : ℝ) (ε / 15)
  constructor
  · -- Show δ > 0
    cases' min_cases (1 : ℝ) (ε / 15) with h2 h2
    · -- Case where 1 < ε / 15
      linarith [h₁]
    · -- Case where ε / 15 ≤ 1
      nlinarith [h₁, show ε / 15 > 0 by positivity]
  · -- Show ∀ x : ℝ, |x - 1| < δ → |f x - f 1| < ε
    intro x hx
    have h2 : |x - 1| < min (1 : ℝ) (ε / 15) := hx
    have h3 : |x - 1| < 1 := by
      cases' min_cases (1 : ℝ) (ε / 15) with h4 h4
      · -- Case where min (1 : ℝ) (ε / 15) = 1
        nlinarith [h4, h2]
      · -- Case where min (1 : ℝ) (ε / 15) = ε / 15
        have h4' : ε / 15 ≤ (1 : ℝ) := by
          nlinarith [h4, show ε / 15 ≥ 0 by positivity, h₁]
        nlinarith [h2, h4']
    have h4 : |f x - f 1| = 5 * |x - 1| * |x + 1| := by
      have h5 : f x = -5 * x ^ 2 - 7 := by
        rw [h₀]
      have h6 : f 1 = -12 := by
        rw [h₀]
        norm_num
      have h7 : f x - f 1 = (-5 * x ^ 2 - 7) - (-12) := by 
        rw [h5, h6]
      have h8 : (-5 * x ^ 2 - 7) - (-12) = -5 * (x ^ 2 - 1) := by
        nlinarith
      have h9 : |f x - f 1| = |(-5 * (x ^ 2 - 1))| := by 
        rw [show f x - f 1 = -5 * (x ^ 2 - 1) by linarith [h7, h8]]
      rw [h9]
      have h10 : |(-5 * (x ^ 2 - 1))| = 5 * |x ^ 2 - 1| := by
        calc
          |(-5 * (x ^ 2 - 1))| = |(-5 : ℝ) * (x ^ 2 - 1)| := by ring_nf
          _ = |(-5 : ℝ)| * |(x ^ 2 - 1)| := by rw [abs_mul]
          _ = (5 : ℝ) * |(x ^ 2 - 1)| := by norm_num
          _ = 5 * |x ^ 2 - 1| := by ring
      rw [h10]
      have h11 : |x ^ 2 - 1| = |x - 1| * |x + 1| := by
        have h12 : x ^ 2 - 1 = (x - 1) * (x + 1) := by
          ring
        rw [h12]
        rw [abs_mul]
        <;> ring_nf <;> simp [abs_mul]
      rw [h11]
      all_goals ring_nf <;> simp [abs_mul]
    have h5 : |x + 1| < 3 := by
      have h6 : 0 < x := by
        linarith [abs_lt.mp h3]
      have h7 : x < 2 := by
        linarith [abs_lt.mp h3]
      have h8 : x + 1 > (1 : ℝ) := by 
        linarith
      have h9 : x + 1 < (3 : ℝ) := by 
        linarith
      apply abs_lt.mpr
      constructor <;> nlinarith
    have h6 : |f x - f 1| < ε := by
      cases' min_cases (1 : ℝ) (ε / 15) with h7 h7
      · -- Case where min (1 : ℝ) (ε / 15) = 1
        have h10 : |x - 1| < (1 : ℝ) := h3
        nlinarith [abs_nonneg (x - 1), abs_nonneg (x + 1), h4, h5, abs_lt.mp h3, h7, h₁]
      · -- Case where min (1 : ℝ) (ε / 15) = ε / 15
        have h10 : |x - 1| < (ε / 15 : ℝ) := by
          cases' abs_lt.mp h2 with h9 h9
          all_goals 
            nlinarith [show ε / 15 > 0 by positivity, h₁]
        have h11 : ε / 15 ≤ (1 : ℝ) := by
          nlinarith [h7, show ε / 15 ≥ 0 by positivity, h₁]
        nlinarith [abs_nonneg (x - 1), abs_nonneg (x + 1), h4, h5, abs_lt.mp h3, h10, h₁]
    linarith
    all_goals linarith
    all_goals linarith