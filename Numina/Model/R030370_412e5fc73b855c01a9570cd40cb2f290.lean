import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_137340 {f : ℝ → ℝ} (hf : f = λ x => -2 * x ^ 2 - 5) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 2| < δ → |f x - f 2| < ε := by
  use min (1 : ℝ) (ε / 10)
  constructor
  · -- Show δ > 0
    cases min_cases (1 : ℝ) (ε / 10) with
    | inl h =>
      linarith
    | inr h =>
      have h1 : ε / 10 > 0 := by linarith
      linarith
  · -- Show the implication
    intro x hx
    have h1 : |x - 2| < min (1 : ℝ) (ε / 10) := hx
    have h2 : |x - 2| < 1 := by
      cases min_cases (1 : ℝ) (ε / 10) with
      | inl h =>
        nlinarith [abs_nonneg (x - 2), h1, h]
      | inr h =>
        nlinarith [abs_nonneg (x - 2), h1, h]
    have h3 : |x - 2| < ε / 10 := by
      cases min_cases (1 : ℝ) (ε / 10) with
      | inl h =>
        nlinarith [abs_nonneg (x - 2), h1, h]
      | inr h =>
        nlinarith [abs_nonneg (x - 2), h1, h]
    -- Show that x is in (1, 3)
    have h4 : x > 1 := by
      cases' abs_lt.mp h2 with h5 h6
      linarith
    have h5 : x < 3 := by
      cases' abs_lt.mp h2 with h5 h6
      linarith
    -- Show that |x + 2| < 5
    have h6 : x + 2 < 5 := by
      nlinarith
    have h7 : x + 2 > 3 := by
      nlinarith
    have h10 : |f x - f 2| = 2 * |x - 2| * |x + 2| := by
      have h8 : f x = -2 * x ^ 2 - 5 := by
        rw [hf]
      have h9 : f 2 = -13 := by
        rw [hf]
        norm_num
      have h11 : (-2 * x ^ 2 - 5 : ℝ) - (-13 : ℝ) = -2 * (x ^ 2 - 4) := by
        ring_nf
      rw [h8, h9]
      rw [h11]
      have h12 : |-2 * (x ^ 2 - 4)| = 2 * |x ^ 2 - 4| := by
        have : |-2 * (x ^ 2 - 4)| = |(-2 : ℝ)| * |x ^ 2 - 4| := by
          simp [abs_mul]
        rw [this]
        norm_num
      have h13 : |x ^ 2 - 4| = |x - 2| * |x + 2| := by
        have h14 : x ^ 2 - 4 = (x - 2) * (x + 2) := by
          ring_nf
        rw [h14]
        have h15 : |(x - 2) * (x + 2)| = |x - 2| * |x + 2| := by
          simp [abs_mul]
        linarith [h15]
      rw [h12, h13]
      all_goals ring
    have h11 : |x + 2| < 5 := by
      have h10 : x + 2 < 5 := by
        nlinarith
      have h11 : x + 2 > -5 := by
        nlinarith
      apply abs_lt.mpr
      constructor <;> nlinarith
    have h12 : 2 * |x - 2| * |x + 2| < ε := by
      have h10 : |x - 2| < ε / 10 := by
        linarith [h3]
      have h11 : |x + 2| < 5 := h11
      nlinarith [abs_nonneg (x - 2), abs_nonneg (x + 2)]
    rw [h10]
    linarith