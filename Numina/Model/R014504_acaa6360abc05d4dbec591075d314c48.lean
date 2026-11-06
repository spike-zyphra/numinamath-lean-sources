import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_142467 (f : ℝ → ℝ) (hf : f = λ x => -2 * x ^ 2 + 9) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 4| < δ → |f x - f 4| < ε := by
  use min (1 : ℝ) (ε / 18)
  constructor
  · -- Show δ > 0
    cases' min_cases (1 : ℝ) (ε / 18) with h1 h2
    · -- Case where 1 < ε / 18
      linarith [h1, hε]
    · -- Case where 1 ≥ ε / 18
      linarith [h2, hε]
  · -- Show that for all x, |x - 4| < δ implies |f x - f 4| < ε
    intro x hx
    have h1 : |x - 4| < min (1 : ℝ) (ε / 18) := hx
    have h2 : |x - 4| < 1 := by
      cases' min_cases (1 : ℝ) (ε / 18) with h11 h12
      · -- Case where min (1 : ℝ) (ε / 18) = 1
        nlinarith [h11, h1]
      · -- Case where min (1 : ℝ) (ε / 18) = ε / 18
        have h2 : ε / 18 ≤ (1 : ℝ) := by linarith [h12]
        nlinarith [h1, h2]
    have h4 : x < 5 := by
      cases' abs_lt.mp h2 with h10 h11
      all_goals linarith
    have h5 : x > 3 := by
      cases' abs_lt.mp h2 with h10 h11
      all_goals linarith
    have h6 : |x + 4| < 9 := by
      have h7 : x + 4 < 9 := by
        linarith [show x < 5 by linarith [h4]]
      have h8 : x + 4 > -9 := by
        nlinarith [show x > 3 by linarith [h5]]
      apply abs_lt.mpr
      constructor <;> linarith
    have h7 : |f x - f 4| = 2 * |x - 4| * |x + 4| := by
      have h11 : f x = -2 * x ^ 2 + 9 := by
        rw [hf]
      have h12 : f 4 = -23 := by
        rw [hf]
        norm_num
      have h13 : f x - f 4 = -2 * (x ^ 2 - 16) := by
        rw [h11, h12]
        ring_nf
      have h14 : |f x - f 4| = |-2 * (x ^ 2 - 16)| := by
        rw [show f x - f 4 = -2 * (x ^ 2 - 16) by linarith [h13]]
      have h15 : |-2 * (x ^ 2 - 16)| = 2 * |x ^ 2 - 16| := by
        calc
          |-2 * (x ^ 2 - 16)| = |(-2 : ℝ) * (x ^ 2 - 16)| := by ring_nf
          _ = |(-2 : ℝ)| * |x ^ 2 - 16| := by rw [abs_mul]
          _ = (2 : ℝ) * |x ^ 2 - 16| := by norm_num
      have h16 : |x ^ 2 - 16| = |x - 4| * |x + 4| := by
        have h17 : x ^ 2 - 16 = (x - 4) * (x + 4) := by
          ring_nf
        rw [h17]
        rw [abs_mul]
        <;> ring_nf
      rw [h14, h15, h16]
      all_goals ring_nf
    have h3 : |x - 4| < ε / 18 := by
      cases' min_cases (1 : ℝ) (ε / 18) with h11 h12
      · -- Case where min (1 : ℝ) (ε / 18) = 1
        have h5 : (1 : ℝ) ≤ ε / 18 := by linarith [h11]
        nlinarith [h1, h5]
      · -- Case where min (1 : ℝ) (ε / 18) = ε / 18
        nlinarith [h1, h12]
    have h8 : |f x - f 4| < ε := by
      rw [h7]
      have h9 : |x - 4| < ε / 18 := h3
      have h10 : |x + 4| < 9 := h6
      nlinarith [abs_nonneg (x - 4), abs_nonneg (x + 4), abs_nonneg (f x - f 4)]
    linarith [h8]