import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_156795 (f : ℝ → ℝ) (hf : f = λ x => -4 * x ^ 2 - 7) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 1| < δ → |f x - f 1| < ε := by 
  use min (1 : ℝ) (ε / 12)
  constructor
  · -- Show δ > 0
    cases' min_cases (1 : ℝ) (ε / 12) with h1 h2
    · -- Case where 1 < ε / 12
      linarith [show ε > 0 by linarith]
    · -- Case where ε / 12 ≤ 1
      linarith [show ε > 0 by linarith]
  · -- Show that ∀ x, |x - 1| < δ → |f x - f 1| < ε
    intro x hx
    have h1 : |x - 1| < min (1 : ℝ) (ε / 12) := hx
    have h2 : |x - 1| < 1 := by
      linarith [h1, min_le_left (1 : ℝ) (ε / 12)]
    have h3 : |x - 1| < ε / 12 := by
      linarith [h1, min_le_right (1 : ℝ) (ε / 12)]
    have h4 : f x = -4 * x ^ 2 - 7 := by
      rw [hf]
    have h5 : f 1 = -11 := by
      rw [hf]
      norm_num
    have h6 : |f x - f 1| = 4 * |x ^ 2 - 1| := by
      rw [h4, h5]
      have h7 : (-4 * x ^ 2 - 7 : ℝ) - (-11 : ℝ) = -4 * (x^2 - 1) := by ring
      rw [h7]
      have h8 : |(-4 * (x ^ 2 - 1) : ℝ)| = 4 * |x ^ 2 - 1| := by
        calc
          |(-4 * (x ^ 2 - 1) : ℝ)| = |(-4 : ℝ) * (x ^ 2 - 1)| := by ring_nf
          _ = |(-4 : ℝ)| * |x ^ 2 - 1| := by rw [abs_mul]
          _ = (4 : ℝ) * |x ^ 2 - 1| := by norm_num
      rw [h8]
    -- Prove |x^2 - 1| < ε / 4
    have h7 : |x ^ 2 - (1 : ℝ)| < ε / 4 := by
      have h7 : |x ^ 2 - (1 : ℝ)| = |x - 1| * |x + 1| := by
        have h13 : x ^ 2 - (1 : ℝ) = (x - 1) * (x + 1) := by
          ring
        rw [h13]
        rw [abs_mul]
        <;> ring_nf <;> norm_num
      rw [h7]
      have h18 : |x + 1| < 3 := by
        have h8 : 0 < x := by
          linarith [abs_lt.mp h2]
        have h9 : x < 2 := by
          linarith [abs_lt.mp h2]
        have h11 : x + 1 < 3 := by
          nlinarith
        have h14 : |x + 1| < 3 := by
          rw [abs_of_pos (by nlinarith)]
          linarith
        exact h14
      have h13' : |x - 1| < ε / 12 := by
        linarith [abs_lt.mp h1, min_le_left (1 : ℝ) (ε / 12), min_le_right (1 : ℝ) (ε / 12)]
      nlinarith [abs_nonneg (x - 1), abs_nonneg (x + 1)]
    linarith [h6, h7]