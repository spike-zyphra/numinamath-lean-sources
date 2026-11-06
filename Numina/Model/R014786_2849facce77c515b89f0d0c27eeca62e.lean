import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_141783 (f : ℝ → ℝ) (hf : f = λ x => 2 * x ^ 2 - 3)
  (ε : ℝ) (hε : ε > 0) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 4| < δ → |f x - f 4| < ε := by

  use min (1 : ℝ) (ε / 18)
  constructor
  · -- Show δ > 0
    cases min_cases (1 : ℝ) (ε / 18) with
    | inl h =>
      linarith
    | inr h =>
      have hε' : ε / 18 > (0 : ℝ) := by
        linarith
      linarith
  · -- Show that ∀ x, |x - 4| < δ → |f x - f 4| < ε
    intro x hx
    have h1 : |x - 4| < min (1 : ℝ) (ε / 18) := hx
    have h3 : |x - 4| < (1 : ℝ) := by
      cases min_cases (1 : ℝ) (ε / 18) with
      | inl h =>
        linarith [abs_lt.mp h1]
      | inr h =>
        linarith [abs_lt.mp h1]
    have h4 : |x - 4| < ε / 18 := by
      cases min_cases (1 : ℝ) (ε / 18) with
      | inl h =>
        linarith [abs_lt.mp h1]
      | inr h =>
        linarith [abs_lt.mp h1]
    have h5 : 3 < x ∧ x < 5 := by
      constructor
      · -- Show 3 < x
        linarith [abs_lt.mp h3]
      · -- Show x < 5
        linarith [abs_lt.mp h3]
    have h6 : |x + 4| < 9 := by
      have h7 : -1 < x - 4 := by linarith [abs_lt.mp h3]
      have h8 : x - 4 < 1 := by linarith [abs_lt.mp h3]
      have h9 : 3 < x := by linarith
      have h10 : x < 5 := by linarith
      have h11 : -9 < x + 4 := by linarith
      have h12 : x + 4 < 9 := by linarith
      apply abs_lt.mpr
      constructor <;> nlinarith
    have h7 : |f x - f 4| = 2 * |x - 4| * |x + 4| := by
      have h8 : f 4 = (29 : ℝ) := by
        rw [hf]
        norm_num
      have h9 : f x = 2 * x ^ 2 - 3 := by
        rw [hf]
      have h10 : f x - f 4 = 2 * (x - 4) * (x + 4) := by
        rw [h9, h8]
        ring_nf
      rw [show f x - f 4 = 2 * (x - 4) * (x + 4) by linarith [h10]]
      have h11 : |2 * (x - 4) * (x + 4)| = 2 * |x - 4| * |x + 4| := by
        calc
          |2 * (x - 4) * (x + 4)| = |(2 * (x - 4)) * (x + 4)| := by ring_nf
          _ = |2 * (x - 4)| * |x + 4| := by rw [abs_mul]
          _ = |(2 : ℝ)| * |x - 4| * |x + 4| := by rw [abs_mul]
          _ = (2 : ℝ) * |x - 4| * |x + 4| := by
            norm_num
            all_goals ring_nf
          _ = 2 * |x - 4| * |x + 4| := by ring_nf
      linarith [abs_nonneg (2 * (x - 4) * (x + 4)), h11, abs_nonneg (x - 4), abs_nonneg (x + 4)]
    have h8 : |f x - f 4| < ε := by
      rw [h7]
      have h9 : |x - 4| < (ε / 18 : ℝ) := h4
      have h10 : |x + 4| < (9 : ℝ) := h6
      have h11 : 2 * |x - 4| * |x + 4| < (2 * (ε / 18 : ℝ) * (9 : ℝ)) := by
        nlinarith [abs_nonneg (x - 4), abs_nonneg (x + 4),
          h9, h10, abs_nonneg (x - 4), abs_nonneg (x + 4)]
      have h12 : (2 * (ε / 18 : ℝ) * (9 : ℝ)) = (ε : ℝ) := by
        linarith
      nlinarith [abs_nonneg (x - 4), abs_nonneg (x + 4),
        h11, h12, abs_nonneg (x - 4), abs_nonneg (x + 4)]
    simpa using h8