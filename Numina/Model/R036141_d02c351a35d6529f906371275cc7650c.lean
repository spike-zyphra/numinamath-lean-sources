import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_137114 (f : ℝ → ℝ) (hf : f = λ x => -5 * x ^ 2 - 8) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 2| < δ → |f x - f 2| < ε := by
  use min (1 : ℝ) (ε / 25)
  constructor
  · -- show δ > 0
    cases' min_cases (1 : ℝ) (ε / 25) with h1 h2
    · -- 1 ≤ ε / 25
      linarith [show 0 < (1 : ℝ) by norm_num, show 0 < ε by linarith]
    · -- ε / 25 ≤ 1
      linarith [show 0 < ε / 25 by linarith, show 0 < (1 : ℝ) by norm_num]
  · -- Show ∀ x, |x - 2| < δ → |f x - f 2| < ε
    intro x hx
    have h1 : |x - 2| < min (1 : ℝ) (ε / 25) := hx
    have h2 : |x - 2| < 1 := by
      cases' min_cases (1 : ℝ) (ε / 25) with h11 h22
      · -- 1 ≤ ε / 25
        nlinarith [h1, h11]
      · -- ε / 25 ≤ 1
        nlinarith [h1, h22]
    have h3 : |x - 2| < ε / 25 := by
      cases' min_cases (1 : ℝ) (ε / 25) with h11 h22
      · -- 1 ≤ ε / 25
        nlinarith [h1, h11]
      · -- ε / 25 ≤ 1
        nlinarith [h1, h22]
    have hfx1 : |f x - f 2| = 5 * |x - 2| * |x + 2| := by
      have h1f : f x = -5 * x ^ 2 - 8 := by
        rw [hf]
      have h2f : f 2 = -28 := by
        rw [hf]
        norm_num
      have h3 : f x - f 2 = -5 * (x ^ 2 - 4) := by
        rw [h1f, h2f]
        ring
      calc
        |f x - f 2| = |(-5 * (x ^ 2 - 4))| := by
          have : f x - f 2 = -5 * (x ^ 2 - 4) := h3
          rw [show f x - f 2 = -5 * (x ^ 2 - 4) by linarith [h3]]
        _ = |-5| * |x ^ 2 - 4| := by
          rw [abs_mul]
        _ = 5 * |x ^ 2 - 4| := by
          norm_num
        _ = 5 * |x - 2| * |x + 2| := by
          have h : x ^ 2 - 4 = (x - 2) * (x + 2) := by ring
          rw [h]
          rw [abs_mul]
          <;> ring
    have h4 : |x + 2| ≤ (5 : ℝ) := by
      have hx1 : 1 < x := by
        linarith [abs_lt.mp h2]
      have hx2 : x < (3 : ℝ) := by
        linarith [abs_lt.mp h2]
      have h46 : |x + 2| = x + 2 := by
        rw [abs_of_pos]
        linarith
      rw [h46]
      all_goals linarith
    rw [hfx1]
    have h7 : 5 * |x - 2| * |x + 2| < ε := by
      have h8 : |x - 2| < ε / 25 := h3
      have h9 : |x + 2| ≤ 5 := h4
      nlinarith [abs_nonneg (x - 2)]
    linarith