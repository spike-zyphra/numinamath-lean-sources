import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_11927 (a : ℝ) :
  {x | x^2 < abs (x - 1) + a} ⊆ {x | -3 < x ∧ x < 3} ↔
  a ≤ 5 := by
  constructor
  · -- Assume {x | x^2 < abs (x - 1) + a} ⊆ {x | -3 < x ∧ x < 3}
    intro h
    by_contra ha
    push_neg at ha
    have h1 : (-3 : ℝ) ∈ {x | x^2 < abs (x - 1) + a} := by
      dsimp
      norm_num
      all_goals
        linarith
    have h3 : (-3 : ℝ) ∈ {x | -3 < x ∧ x < 3} := by 
      apply h
      exact h1
    norm_num at h3
  · -- Assume a ≤ 5
    intro ha
    intro x hx
    have h1 : x^2 < abs (x - 1) + a := by
      simpa using hx
    by_cases h2 : x ≥ 1
    · -- x ≥ 1.
      have h3 : abs (x - 1) = x - 1 := by
        rw [abs_of_nonneg]
        linarith
      rw [h3] at h1
      constructor
      · -- Show $-3 < x$.
        nlinarith
      · -- Show $x < 3$.
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 1), sq_nonneg (x + 2)]
    · -- x < 1.
      have h3 : abs (x - 1) = 1 - x := by
        rw [abs_of_neg]
        linarith
        all_goals
        linarith
      rw [h3] at h1
      constructor
      · -- Show $-3 < x$.
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 2)]
      · -- Show $x < 3$.
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 2)]