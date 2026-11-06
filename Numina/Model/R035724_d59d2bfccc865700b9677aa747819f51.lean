import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_133411 (f : ℝ → ℝ) (hf : f = λ x => -4 * x ^ 2 - 6) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 1| < δ → |f x - f 1| < ε := by
  use min (1:ℝ) (ε / 12)
  constructor
  · -- Show δ > 0
    cases min_cases (1:ℝ) (ε / 12) with
    | inl h =>
      nlinarith
    | inr h =>
      nlinarith
  · -- Show that for all x, if |x - 1| < δ, then |f x - f 1| < ε
    intro x hx
    have h1 : |x - 1| < min (1:ℝ) (ε / 12) := by
      simpa using hx
    have h2 : |x - 1| < 1 := by
      linarith [show min (1:ℝ) (ε / 12) ≤ (1:ℝ) by
        cases min_cases (1:ℝ) (ε / 12) with
        | inl h =>
          linarith
        | inr h =>
          nlinarith
      ]
    -- From |x - 1| < 1, we have 0 < x < 2
    have h3 : -1 < x - 1 := by
      linarith [abs_lt.mp h2]
    have h4 : x - 1 < 1 := by
      linarith [abs_lt.mp h2]
    have h5 : 0 < x := by
      nlinarith
    have h6 : x < 2 := by
      nlinarith
    -- From 0 < x < 2, we have 1 < x + 1 < 3, so |x + 1| < 3
    have h7 : x + 1 < 3 := by
      nlinarith
    have h8 : x + 1 > 1 := by
      nlinarith
    have h8 : |x + 1| < 3 := by
      rw [abs_of_pos (show x + 1 > 0 by linarith)]
      linarith
    have h9 : f x = -4 * x ^ 2 - 6 := by
      rw [hf]
    have h10 : f 1 = -10 := by
      rw [hf]
      norm_num
    have h11 : |f x - f 1| = 4 * |x - 1| * |x + 1| := by
      rw [h9, h10]
      have h12 : (-4 * x ^ 2 - 6: ℝ) - (-10) = -4 * (x^2 - 1) := by
        ring
      have h13 : |(-4 * (x^2 - 1) : ℝ)| = (4 * |x^2 - 1| : ℝ) := by
        calc
          |(-4 * (x^2 - 1) : ℝ)| = |(-4: ℝ) * (x^2 - 1)| := by ring
          _ = |(-4: ℝ)| * |x^2 - 1| := by
            rw [abs_mul]
          _ = (4 * |x^2 - 1| : ℝ) := by
            norm_num
      rw [h12, h13]
      have h14 : |x^2 - 1| = |x - 1| * |x + 1| := by
        have h15 : x^2 - 1 = (x - 1) * (x + 1) := by ring
        rw [h15]
        rw [abs_mul]
        <;> ring
      rw [h14]
      all_goals ring
    -- Show that |f x - f 1| < ε
    have h15 : |x - 1| < ε / 12 := by
      linarith [show min (1:ℝ) (ε / 12) ≤ ε / 12 by
        cases min_cases (1:ℝ) (ε / 12) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      ]
    have h18 : 4 * |x - 1| * |x + 1| < ε := by
      have h19 : |x + 1| < 3 := h8
      have h20 : |x - 1| ≥ 0 := abs_nonneg (x - 1)
      have h21 : |x + 1| ≥ 0 := abs_nonneg (x + 1)
      nlinarith [h15, h19, mul_nonneg h20 h21, abs_nonneg (x ^ 2 - 1)]
    have h16 : |f x - f 1| < ε := by
      have h17 : |f x - f 1| = 4 * |x - 1| * |x + 1| := h11
      have h18' : 4 * |x - 1| * |x + 1| < ε := h18
      linarith [h17, h18']
    linarith [h16]