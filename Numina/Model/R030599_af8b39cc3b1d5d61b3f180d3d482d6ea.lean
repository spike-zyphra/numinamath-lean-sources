import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_122083 {f : ℝ → ℝ} (hf : f = λ x => 4 * x ^ 2 - 2) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 5| < δ → |f x - f 5| < ε := by
  use min (1 : ℝ) (ε / 44)
  constructor
  · -- Show δ > 0
    cases min_cases (1 : ℝ) (ε / 44) with
    | inl h =>
      linarith
    | inr h =>
      have : ε / 44 > 0 := by linarith
      linarith
  · -- Show ∀ x, |x - 5| < δ → |f x - f 5| < ε
    intro x hx
    have h1 : |x - 5| < min (1 : ℝ) (ε / 44) := hx
    have h2 : |x - 5| < (1 : ℝ) := by
      cases min_cases (1 : ℝ) (ε / 44) with
      | inl h =>
        nlinarith [show (1 : ℝ) > 0 by norm_num, h1]
      | inr h =>
        nlinarith [show (1 : ℝ) > 0 by norm_num, h1, show ε / 44 ≤ (1 : ℝ) by
          cases min_cases (1 : ℝ) (ε / 44) with
          | inl h9 =>
            linarith
          | inr h9 =>
            linarith
        ]
    have h3 : x > (4 : ℝ) := by
      linarith [abs_lt.mp h2]
    have h4 : x < (6 : ℝ) := by
      linarith [abs_lt.mp h2]
    have h5 : x + 5 > (9 : ℝ) := by
      linarith
    have h6 : x + 5 < (11 : ℝ) := by
      linarith
    have h7 : |x + 5| < (11 : ℝ) := by
      rw [abs_of_pos (show x + 5 > 0 by linarith)]
      linarith
    have h8 : f x = 4 * x ^ 2 - 2 := by
      rw [hf]
    have h9 : f 5 = (4 * (5 : ℝ) ^ 2 - 2 : ℝ) := by
      rw [hf]
    have h10 : |f x - f 5| = 4 * |x ^ 2 - 25| := by
      rw [h8, h9]
      have h11 : (4 * x ^ 2 - 2 : ℝ) - (4 * (5 : ℝ) ^ 2 - 2) = 4 * (x ^ 2 - 25) := by
        ring_nf
      rw [h11]
      have h12 : |(4 * (x ^ 2 - 25) : ℝ)| = (4 : ℝ) * |x ^ 2 - 25| := by
        simp [abs_mul]
      linarith
    have h11 : |x ^ 2 - 25| = |x - 5| * |x + 5| := by
      have h12 : x ^ 2 - 25 = (x - 5) * (x + 5) := by
        ring_nf
      rw [h12]
      have h13 : |(x - 5 : ℝ) * (x + 5)| = |x - 5| * |x + 5| := by
        simp [abs_mul]
      linarith
    rw [h10, h11]
    have h12 : |x - 5| < ε / 44 := by
      cases min_cases (1 : ℝ) (ε / 44) with
      | inl h =>
        nlinarith [show (1 : ℝ) > 0 by norm_num, h1, show ε / 44 > 0 by linarith]
      | inr h =>
        nlinarith [show (1 : ℝ) > 0 by norm_num, h1]
    nlinarith [abs_nonneg (x - 5), abs_nonneg (x + 5), h7, h12]