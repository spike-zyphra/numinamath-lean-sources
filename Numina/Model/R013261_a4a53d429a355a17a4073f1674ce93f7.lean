import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_141171 {f : ℝ → ℝ} (hf : f = λ x => 4 * x ^ 2 + 4) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 9| < δ → |f x - f 9| < ε := by
  use min (1 : ℝ) (ε / 76)
  constructor
  · -- Show δ > 0
    cases min_cases (1 : ℝ) (ε / 76) with
    | inl h =>
      linarith -- 1 > 0
    | inr h =>
      have h1 : ε / 76 > 0 := by
        linarith
      linarith
  · -- Show the implication ∀ x, |x - 9| < δ → |f x - f 9| < ε
    intro x hx
    have h1 : |x - 9| < min (1 : ℝ) (ε / 76) := hx
    have h2 : |x - 9| < 1 := by
      have h3 : min (1 : ℝ) (ε / 76) ≤ (1 : ℝ) := by
        cases min_cases (1 : ℝ) (ε / 76) with
        | inl h1 =>
          linarith
        | inr h1 =>
          linarith
      nlinarith
    have h410 : |x - 9| < ε / 76 := by
      cases min_cases (1 : ℝ) (ε / 76) with
      | inl h =>
        nlinarith [abs_lt.mp h1, show ε / 76 > 0 by linarith]
      | inr h =>
        nlinarith [abs_lt.mp h1]
    have h31 : f 9 = 328 := by
      rw [hf]
      norm_num
    have h41 : f x = 4 * x ^ 2 + 4 := by
      rw [hf]
      all_goals
        simp
    have h51 : |f x - f 9| = 4 * |x - 9| * |x + 9| := by
      rw [h41, h31]
      have h42 : (4 * x ^ 2 + 4 : ℝ) - 328 = 4 * (x ^ 2 - 81) := by
        ring
      rw [h42]
      have h43 : 4 * (x ^ 2 - 81) = 4 * (x - 9) * (x + 9) := by
        ring
      rw [h43]
      have h44 : |(4 * (x - 9) * (x + 9) : ℝ)| = 4 * |x - 9| * |x + 9| := by
        have h11 : |(4 * (x - 9) * (x + 9) : ℝ)| = 4 * |(x - 9 : ℝ)| * |(x + 9 : ℝ)| := by
          calc
            |(4 * (x - 9) * (x + 9) : ℝ)| = |(4 * (x - 9) : ℝ) * (x + 9)| := by ring_nf
            _ = |(4 * (x - 9) : ℝ)| * |(x + 9 : ℝ)| := by
              rw [abs_mul]
            _ = |(4 : ℝ) * (x - 9)| * |(x + 9 : ℝ)|  := by ring_nf
            _ = |(4 : ℝ)| * |(x - 9 : ℝ)| * |(x + 9 : ℝ)| := by
              rw [abs_mul]
            _ = (4 : ℝ) * |(x - 9 : ℝ)| * |(x + 9 : ℝ)| := by
              norm_num
            _ = 4 * |(x - 9 : ℝ)| * |(x + 9 : ℝ)| := by ring
        linarith
      linarith
    have h411 : |x + 9| < 19 := by
      have h61 : 8 < x := by
        linarith [abs_lt.mp h2]
      have h62 : x < 10 := by
        linarith [abs_lt.mp h2]
      have h63 : x + 9 > (17 : ℝ) := by linarith
      have h64 : x + 9 < (19 : ℝ) := by linarith
      have h65 : -19 < x + 9 := by linarith
      apply abs_lt.mpr
      constructor <;> linarith
    calc
      |f x - f 9| = 4 * |x - 9| * |x + 9| := by
        rw [h51]
      _ < 4 * (ε / 76) * 19 := by
        have h81 : |x - 9| < ε / 76 := h410
        have h82 : |x + 9| < 19 := h411
        nlinarith [abs_nonneg (x - 9 : ℝ), abs_nonneg (x + 9 : ℝ)]
      _ = ε := by
        ring