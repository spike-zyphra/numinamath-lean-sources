import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_143612 (f : ℝ → ℝ) (hf : f = λ x => -3 * x ^ 2 - 9) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 3| < δ → |f x - f 3| < ε := by
  use min (1 : ℝ) (ε / 21)
  constructor
  · -- Show δ > 0
    cases min_cases (1 : ℝ) (ε / 21) with
    | inl h =>
      linarith [show (1 : ℝ) > 0 by norm_num, hε]
    | inr h =>
      have h2 : ε / 21 > 0 := by linarith
      linarith [h2, hε]
  · -- Show ∀ x, |x - 3| < δ → |f x - f 3| < ε
    intro x h
    have h1 : |x - 3| < min (1 : ℝ) (ε / 21) := h
    have h2 : |x - 3| < (1 : ℝ) := by
      cases min_cases (1 : ℝ) (ε / 21) with
      | inl hmin =>
        linarith [h1, hmin]
      | inr hmin =>
        have h3 : ε / 21 ≤ (1 : ℝ) := by
          linarith [hmin]
        linarith [h1, h3]
    -- From |x - 3| < 1, we have 2 < x < 4, so 5 < x + 3 < 7, which means |x + 3| < 7
    have h5 : 2 < x := by
      linarith [abs_lt.mp h2]
    have h6 : x < 4 := by
      linarith [abs_lt.mp h2]
    have h7 : 5 < x + 3 := by linarith
    have h8 : x + 3 < 7 := by linarith
    have h9 : |x + 3| < (7 : ℝ) := by
      have h10 : -7 < x + 3 := by linarith
      have h11 : x + 3 < 7 := by linarith
      apply abs_lt.mpr
      constructor <;> linarith
    have h10 : |x - 3| < ε / 21 := by
      cases min_cases (1 : ℝ) (ε / 21) with
      | inl hmin =>
        linarith [h1, hmin, show (1 : ℝ) > 0 by norm_num, show ε / 21 > 0 by linarith [hε]]
      | inr hmin =>
        linarith [h1, hmin]
    have hfx : |f x - f 3| = 3 * |x - 3| * |x + 3| := by
      have h1 : f x = -3 * x ^ 2 - 9 := by
        rw [hf]
      have h2 : f 3 = -36 := by
        rw [hf]
        norm_num
      have eq : f x - f 3 = -3 * (x^2 - 9) := by
        rw [h1, h2]
        ring_nf
      have eq2 : |f x - f 3| = 3 * |x - 3| * |x + 3| := by
        rw [eq]
        have eq3 : |-3 * (x^2 - 9)| = 3 * |x^2 - 9| := by
          calc
            |-3 * (x^2 - 9)| = |(-3 : ℝ) * (x^2 - 9)| := by ring_nf
            _ = |(-3 : ℝ)| * |x^2 - 9| := by rw [abs_mul]
            _ = 3 * |x^2 - 9| := by norm_num
        have eq4 : |x^2 - 9| = |x - 3| * |x + 3| := by
          have eq5 : x^2 - 9 = (x - 3) * (x + 3) := by ring_nf
          rw [eq5]
          rw [abs_mul]
          <;> ring_nf
        rw [eq3, eq4]
        <;> ring_nf
      linarith [eq2]
    have h11 : |f x - f 3| < ε := by
      rw [hfx]
      have h14 : 3 * |x - 3| * |x + 3| < ε := by
        have h15 : |x - 3| < ε / 21 := h10
        have h16 : |x + 3| < (7 : ℝ) := h9
        nlinarith [abs_nonneg (x - 3), abs_nonneg (x + 3), h15, h16, hε]
      linarith [h14, hfx]
    simpa using h11