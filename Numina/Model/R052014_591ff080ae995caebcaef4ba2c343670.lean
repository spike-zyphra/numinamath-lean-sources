import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_10457 :
  {x : ℝ | ∃ y, x^2 + y^2 < 4} ⊆ {x : ℝ | ∃ y, x * y + 4 > 2 * x + 2 * y} ∧
  ¬ ({x : ℝ | ∃ y, x * y + 4 > 2 * x + 2 * y} ⊆ {x : ℝ | ∃ y, x^2 + y^2 < 4}) := by
  constructor
  · -- Suppose x ∈ {x : ℝ | ∃ y, x^2 + y^2 < 4}, we need to show x ∈ {x : ℝ | ∃ y, x * y + 4 > 2 * x + 2 * y}
    intro x hx
    rcases hx with ⟨y, hy⟩
    have h1 : x < 2 := by nlinarith [sq_nonneg (x), sq_nonneg (y)]
    have h2 : x > -2 := by nlinarith [sq_nonneg (x), sq_nonneg (y)]
    use 0
    nlinarith
  · -- Now prove that it's not necessary.
    intro h
    have h1 : (3 : ℝ) ∈ {x : ℝ | ∃ y, x * y + 4 > 2 * x + 2 * y} := by
      use 3
      norm_num
    have h2 : (3 : ℝ) ∉ {x : ℝ | ∃ y, x^2 + y^2 < 4} := by
      intro hx
      rcases hx with ⟨y, hy⟩
      have : (3 : ℝ) ^ 2 + y ^ 2 >= 4 := by
        nlinarith [sq_nonneg (y)]
      linarith
    have h3 : (3 : ℝ) ∈ {x : ℝ | ∃ y, x^2 + y^2 < 4} := by
      apply h
      exact h1
    contradiction