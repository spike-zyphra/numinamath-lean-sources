import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_288775 : IsLeast {m : ℝ | ∃ a b : ℝ, ∀ x ∈ Icc (-1) 1, |x^2 + a * x + b| ≤ m * (x^2 + 1)} (1/3) := by 
  constructor
  · -- Show 1/3 is in the set
    use 0, -1 / 3
    intro x hx
    have h1 : -1 ≤ x := by
      have h1 := hx.1
      linarith
    have h2 : x ≤ 1 := by
      have h2 := hx.2
      linarith
    have h3 : 0 ≤ x ^ 2 := by nlinarith
    have h4 : x ^ 2 ≤ 1 := by nlinarith
    have h5 : x ^ 2 + (0 : ℝ) * x + (-1/3 : ℝ) = x^2 - 1/3 := by ring
    have h6 : |x ^ 2 + (0 : ℝ) * x + (-1/3 : ℝ)| = |x ^ 2 - 1/3| := by rw [h5]
    have h7 : |x ^ 2 - 1 / 3| ≤ (1 / 3) * (x ^ 2 + 1) := by
      by_cases h : x ^ 2 - 1/3 ≥ 0
      · -- x ^ 2 - 1/3 ≥ 0
        rw [abs_of_nonneg h]
        nlinarith
      · -- x ^ 2 - 1/3 < 0
        rw [abs_of_neg (show x^2 - 1/3 < 0 by linarith)]
        nlinarith
    rw [h6]
    linarith [h7]
  · -- Show any m in the set ≥ 1/3
    intro m hm
    rcases hm with ⟨a, b, h⟩
    have h1 := h 1 (by norm_num)
    have h2 := h (-1) (by norm_num)
    have h3 := h 0 (by norm_num)
    norm_num [abs_le] at h1 h2 h3
    nlinarith