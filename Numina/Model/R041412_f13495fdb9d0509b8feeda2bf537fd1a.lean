import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_137577 (f : ℝ → ℝ) (hf : f = λ x => 5 * x ^ 2 + 5) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 8| < δ → |f x - f 8| < ε := by
  use min (1 : ℝ) (ε / 85)
  constructor
  · -- Show δ > 0
    cases min_cases (1 : ℝ) (ε / 85) with
    | inl h =>
      linarith [hε]
    | inr h =>
      have h2 : ε / 85 > 0 := by linarith [hε]
      linarith [h2]
  · -- Show that ∀ x, |x - 8| < δ → |f x - f 8| < ε
    intro x hx
    have h1 : |x - 8| < min (1 : ℝ) (ε / 85) := hx
    have h2 : |x - 8| < 1 := by
      cases min_cases (1 : ℝ) (ε / 85) with
      | inl h =>
        linarith [h1, h]
      | inr h =>
        linarith [h1, show ε / 85 ≤ (1 : ℝ) by linarith [h]]
    have h3 : x > 7 := by
      linarith [abs_lt.mp h2]
    have h4 : x < 9 := by
      linarith [abs_lt.mp h2]
    have h7 : |x + 8| < 17 := by
      have h5 : x + 8 < 17 := by 
        linarith
      have h6 : x + 8 > 15 := by 
        linarith
      rw [abs_of_pos (by linarith : x + 8 > 0)]
      linarith
    have h8 : |f x - f 8| = 5 * |x - 8| * |x + 8| := by
      have h9 : f x = 5 * x ^ 2 + 5 := by 
        rw [hf]
      have h10 : f 8 = 5 * (8: ℝ) ^ 2 + 5 := by 
        rw [hf]
      have h11 : |f x - f 8| = |5 * x ^ 2 + 5 - (5 * (8: ℝ) ^ 2 + 5)| := by
        rw [h9, h10]
      have h12 : 5 * x ^ 2 + 5 - (5 * (8: ℝ) ^ 2 + 5) = 5 * (x ^ 2 - 64) := by 
        ring_nf
      have h13 : |5 * x ^ 2 + 5 - (5 * (8: ℝ) ^ 2 + 5)| = |5 * (x ^ 2 - 64)| := by 
        rw [h12]
      have h14 : |5 * (x ^ 2 - 64)| = 5 * |x ^ 2 - 64| := by 
        simp [abs_mul]
      have h15 : |x ^ 2 - 64| = |x - 8| * |x + 8| := by 
        have h16 : x ^ 2 - (64 : ℝ) = (x - 8) * (x + 8) := by 
          ring_nf
        rw [show x ^ 2 - (64 : ℝ) = (x - 8) * (x + 8) by linarith [h16]]
        simp [abs_mul]
        <;> ring
      rw [h11, h13, h14, h15]
      all_goals ring_nf <;> simp
    rw [h8]
    cases min_cases (1 : ℝ) (ε / 85) with
    | inl h =>
      have h9 : ε / 85 ≥ (1 : ℝ) := by 
        linarith [h]
      have h10 : |x - 8| < (1 : ℝ) := by 
        linarith [h1, h]
      nlinarith [abs_nonneg (x - 8), abs_nonneg (x + 8), h7, h10, mul_pos (show (0 : ℝ) < 5 by norm_num) (show (0 : ℝ) < 1 by norm_num), hε, h9]
    | inr h =>
      have h11 : |x - 8| < ε / 85 := by 
        linarith [h1, h]
      nlinarith [abs_nonneg (x - 8), abs_nonneg (x + 8), h7, h11, mul_pos (show (0 : ℝ) < 5 by norm_num) (show (0 : ℝ) < 1 by norm_num), hε]