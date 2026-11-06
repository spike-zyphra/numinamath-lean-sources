import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_144181 (f : ℝ → ℝ) (hf : f = λ x => -2 * x ^ 2 - 4)
  (ε : ℝ) (hε : ε > 0) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 3| < δ → |f x - f 3| < ε := by
  use min (1 : ℝ) (ε / 14)
  constructor
  · -- Show δ > 0
    cases min_cases (1 : ℝ) (ε / 14) with
    | inl h =>
      linarith [show ε > 0 by linarith, h]
    | inr h =>
      have h2 : ε / 14 > 0 := by linarith
      linarith [h2, h]
  · -- Show ∀ x, |x - 3| < δ → |f x - f 3| < ε
    intro x hx
    have h1 : |x - 3| < min (1 : ℝ) (ε / 14) := hx
    have h2 : |x - 3| < (1 : ℝ) := by
      cases min_cases (1 : ℝ) (ε / 14) with
      | inl hmin =>
        linarith [h1, hmin]
      | inr hmin =>
        linarith [h1, hmin, show ε / 14 > 0 by linarith]
    have h3 : |x - 3| < (ε / 14 : ℝ) := by
      cases min_cases (1 : ℝ) (ε / 14) with
      | inl hmin =>
        linarith [h1, hmin, show ε / 14 > 0 by linarith]
      | inr hmin =>
        linarith [h1, hmin]
    have h4 : 2 < x := by
      linarith [abs_lt.mp h2]
    have h5 : x < (4 : ℝ) := by
      linarith [abs_lt.mp h2]
    have h6 : x + 3 < (7 : ℝ) := by
      linarith
    have h7 : (5 : ℝ) < x + 3 := by
      linarith
    have hfx1 : f x = -2 * x ^ 2 - 4 := by
      rw [hf]
    have hf3 : f 3 = -22 := by
      rw [hf]
      norm_num
    have h8 : |f x - f 3| = 2 * |x - 3| * |x + 3| := by
      rw [hfx1, hf3]
      have h9 : (-2 * x ^ 2 - 4 : ℝ) - (-22 : ℝ) = -2 * (x ^ 2 - 9) := by
        ring_nf
      rw [h9]
      have h10 : |-2 * (x ^ 2 - 9)| = 2 * |x ^ 2 - 9| := by
        calc
          |-2 * (x ^ 2 - 9)| = |(-2 : ℝ) * (x ^ 2 - 9)| := by ring_nf
          _ = |(-2 : ℝ)| * |x ^ 2 - 9| := by rw [abs_mul]
          _ = (2 : ℝ) * |x ^ 2 - 9| := by norm_num
      rw [h10]
      have h11 : |x ^ 2 - 9| = |x - 3| * |x + 3| := by
        have h12 : x ^ 2 - 9 = (x - 3) * (x + 3) := by
          ring_nf
        rw [h12]
        rw [abs_mul]
        <;> ring_nf
      rw [h11]
      all_goals ring_nf
    have h81 : |x + 3| < 7 := by
      rw [abs_lt]
      constructor
      · -- Show -7 < x + 3
        linarith
      · -- Show x + 3 < 7
        linarith
    have h9 : |f x - f 3| < ε := by
      rw [h8]
      have h10 : |x - 3| < (ε / 14 : ℝ) := h3
      have h11 : |x + 3| < 7 := h81
      nlinarith [abs_nonneg (x - 3), abs_nonneg (x + 3), abs_nonneg (f x - f 3)]
    exact h9