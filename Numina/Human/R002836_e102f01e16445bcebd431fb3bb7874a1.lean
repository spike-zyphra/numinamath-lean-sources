import Mathlib

theorem algebra_120066 (a b : ℝ) (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ a * x1 - b > x1 ^ 2 + a * x1 + b ∧
    a * x2 - b > x2 ^ 2 + a * x2 + b) :
    ∃ x3 : ℝ, x3 ≠ 0 ∧ a * x3 - b > x3 ^ 2 + a * x3 + b := by 
  rcases h with ⟨x1, x2, hx1x2, hx1, hx2⟩
  by_cases h1 : x1 = 0
  · -- Suppose x1 = 0, then x2 ≠ 0 because x1 ≠ x2
    have h2 : x2 ≠ 0 := by
      intro h
      apply hx1x2
      linarith
    refine ⟨x2, h2, hx2⟩
  · -- Suppose x1 ≠ 0, then we can take x3 = x1
    refine ⟨x1, by intro h; apply h1; linarith, hx1⟩