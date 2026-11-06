import Mathlib

open Real Set
open scoped Topology

theorem calculus_125597 {f : ℝ → ℝ} (hf : f = λ x => 2 * x ^ 2 - 4) (ε : ℝ)
  (hε : ε > 0) : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - 3| < δ → |f x - f 3| < ε := by
  use min (1 : ℝ) (ε / 14)
  constructor
  · -- Show δ > 0
    cases min_cases (1 : ℝ) (ε / 14) with
    | inl h =>
      linarith
    | inr h =>
      linarith
  · -- Show that for all x, if |x - 3| < δ, then |f x - f 3| < ε
    intro x h
    have hx1 : |x - 3| < min (1 : ℝ) (ε / 14) := h
    have h1 : |x - 3| < (1 : ℝ) := by
      have h3 : min (1 : ℝ) (ε / 14) ≤ (1 : ℝ) := by 
        cases min_cases (1 : ℝ) (ε / 14) with
        | inl h => 
          linarith
        | inr h => 
          linarith
      have h4 : |x - 3| < min (1 : ℝ) (ε / 14) := hx1 
      linarith [h4, h3]
    have h2 : |x - 3| < ε / 14 := by
      have h4 : min (1 : ℝ) (ε / 14) ≤ (ε / 14 : ℝ) := by 
        cases min_cases (1 : ℝ) (ε / 14) with
        | inl h => 
          linarith
        | inr h => 
          linarith
      have h5 : |x - 3| < min (1 : ℝ) (ε / 14) := hx1 
      linarith [h5, h4]
    have hx11 : 2 < x := by 
      linarith [abs_lt.mp h1]
    have hx22 : x < 4 := by 
      linarith [abs_lt.mp h1]
    have hx33 : |x + 3| < (7 : ℝ) := by 
      rw [abs_lt]
      constructor
      · -- Show -7 < x + 3
        linarith 
      · -- Show x + 3 < 7
        linarith 
    have h3 : f x = 2 * x ^ 2 - 4 := by 
      rw [hf]
    have h4 : f 3 = (14 : ℝ) := by 
      rw [hf]
      norm_num 
    have h5 : |f x - f 3| = 2 * |x - 3| * |x + 3| := by 
      rw [h3, h4] 
      have h6 : (2 * x ^ 2 - 4 : ℝ) - (14 : ℝ) = 2 * (x ^ 2 - 9) := by 
        linarith 
      have h7 : |(2 * x ^ 2 - 4 : ℝ) - (14 : ℝ)| = |2 * (x ^ 2 - 9)| := by 
        rw [h6] 
      rw [h7] 
      have h8 : |(2 * (x ^ 2 - 9) : ℝ)| = |(2 : ℝ)| * |(x ^ 2 - 9 : ℝ)| := by 
        rw [abs_mul] 
      have h9 : |(2 : ℝ)| = (2 : ℝ) := by 
        norm_num [abs_of_nonneg] 
      have h10 : |(x ^ 2 - 9 : ℝ)| = |x - 3| * |x + 3| := by 
        have h11 : x ^ 2 - 9 = (x - 3) * (x + 3) := by 
          nlinarith 
        rw [h11] 
        rw [abs_mul] 
        <;> ring_nf 
      rw [h8, h9, h10] 
      <;> ring 
    rw [h5] 
    have h7' : (2 * |x - 3| * |x + 3| : ℝ) < ε := by 
      have h11 : |x - 3| < ε / 14 := h2 
      have h12 : |x + 3| < (7 : ℝ) := hx33 
      nlinarith [abs_nonneg (x - 3), abs_nonneg (x + 3)]
    linarith [h7']