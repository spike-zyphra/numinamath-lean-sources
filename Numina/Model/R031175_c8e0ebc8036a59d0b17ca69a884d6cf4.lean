import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_272337 {x : ℝ} :
  (x-2)*(x+1)*(x+3) > 0 ↔ x ∈ Ioo (-3) (-1) ∪ Ioi 2 := by
  constructor
  · -- Assume (x-2)*(x+1)*(x+3) > 0, prove x ∈ (-3,-1)∪(2,∞)
    intro h
    have h1 : (x - 2) * (x + 1) * (x + 3) > 0 := h
    have h2 : x > -3 := by
      by_contra h2
      push_neg at h2
      nlinarith [sq_nonneg (x + 3), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x + 2)]
    by_cases h3 : x < -1
    · -- x < -1
      left
      constructor
      · -- Show -3 < x
        nlinarith
      · -- Show x < -1
        nlinarith
    · -- x ≥ -1
      have h4 : x ≥ -1 := by linarith
      have h5 : x > (2 : ℝ) := by
        by_contra h5
        push_neg at h5
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x + 3), sq_nonneg (x - 1)]
      right
      exact h5
  · -- Assume x ∈ (-3,-1)∪(2,∞), prove (x-2)*(x+1)*(x+3) > 0
    rintro (h | h)
    · -- x ∈ (-3, -1)
      rcases h with ⟨h1, h2⟩
      have h3 : x + 3 > 0 := by linarith
      have h4 : x + 1 < 0 := by linarith
      have h5 : x - 2 < 0 := by linarith
      have h6 : (x - 2) * (x + 1) * (x + 3) > 0 := by
        have h7 : (x - 2) * (x + 1) > 0 := by nlinarith
        nlinarith
      linarith
    · -- x > 2
      have h3 : x > 2 := by
        simpa using h
      have h4 : x - 2 > 0 := by linarith
      have h5 : x + 1 > 0 := by linarith
      have h6 : x + 3 > 0 := by linarith
      have h7 : (x - 2) * (x + 1) * (x + 3) > 0 := by
        positivity
      linarith