import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_144570 :
  ∫ x in (-2)..2, max (x^2) (8 - x^2) - min (x^2) (8 - x^2) = 64/3 := by
  have h : ∀ x : ℝ, -2 ≤ x ∧ x ≤ 2 → max (x ^ 2) (8 - x ^ 2) - min (x ^ 2) (8 - x ^ 2) = 8 - 2 * x ^ 2 := by
    intro x hx
    have h1 : x ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg (x : ℝ), hx.1, hx.2]
    have h2 : 8 - x^2 ≥ x^2 := by
      nlinarith
    have h3 : max (x ^ 2) (8 - x ^ 2) = 8 - x^2 := by
      apply max_eq_right
      linarith
    have h4 : min (x ^ 2) (8 - x^2) = x^2 := by
      apply min_eq_left
      linarith
    rw [h3, h4]
    all_goals nlinarith

  have h2 : ∫ x in (-2)..2, max (x^2) (8 - x^2) - min (x^2) (8 - x^2) = ∫ x in (-2)..2, (8 - 2 * x ^ 2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx1 : -2 ≤ x := by
      have h1 : x ∈ Set.Icc (-2 : ℝ) 2 := by
        simpa using hx
      exact h1.1
    have hx2 : x ≤ 2 := by
      have h1 : x ∈ Set.Icc (-2 : ℝ) 2 := by
        simpa using hx
      exact h1.2
    specialize h x ⟨hx1, hx2⟩
    simpa using h
  rw [h2]
  norm_num [intervalIntegral.integral_const, mul_comm]
  all_goals norm_num