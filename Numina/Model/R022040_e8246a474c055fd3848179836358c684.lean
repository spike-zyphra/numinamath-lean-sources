import Mathlib

theorem algebra_129653 (x y z : ℝ) (h₀ : x + y + z = 5) (h₁ : x * y + y * z + z * x = 3) :
    x ∈ Set.Icc (-1) (13 / 3) ∧ y ∈ Set.Icc (-1) (13 / 3) ∧ z ∈ Set.Icc (-1) (13 / 3) := by

  constructor
  · -- Show x ∈ Set.Icc (-1) (13 / 3)
    have h2 : -1 ≤ x ∧ x ≤ 13 / 3 := by
      constructor
      · -- Prove -1 ≤ x
        nlinarith [sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (x - z),
            h₀, h₁]
      · -- Prove x ≤ 13 / 3
        nlinarith [sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (x - z),
            h₀, h₁]
    exact h2
  constructor
  · -- Show y ∈ Set.Icc (-1) (13 / 3)
    have h3 : -1 ≤ y ∧ y ≤ 13 / 3 := by
      constructor
      · -- Prove -1 ≤ y
        nlinarith [sq_nonneg (x - z), sq_nonneg (y - x), sq_nonneg (y - z),
            h₀, h₁]
      · -- Prove y ≤ 13 / 3
        nlinarith [sq_nonneg (x - z), sq_nonneg (y - x), sq_nonneg (y - z),
            h₀, h₁]
    exact h3
  · -- Show z ∈ Set.Icc (-1) (13 / 3)
    have h4 : -1 ≤ z ∧ z ≤ 13 / 3 := by
      constructor
      · -- Prove -1 ≤ z
        nlinarith [sq_nonneg (x - y), sq_nonneg (z - x), sq_nonneg (z - y),
            h₀, h₁]
      · -- Prove z ≤ 13 / 3
        nlinarith [sq_nonneg (x - y), sq_nonneg (z - x), sq_nonneg (z - y),
            h₀, h₁]
    exact h4