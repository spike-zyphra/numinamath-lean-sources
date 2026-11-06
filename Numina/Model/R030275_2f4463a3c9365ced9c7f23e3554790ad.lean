import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_87681 :
  ∀ x ∈ Ici 1, x^3 - 5 * x^2 + 8 * x - 4 ≥ 0 ∧
  IsLeast {y | ∃ a b : ℝ, a ∈ Ici 1 ∧ b ∈ Ici 1 ∧ y = a * b * (a + b - 10) + 8 * (a + b)} 8 := by
  intro x hx
  constructor
  · -- Show that the expression x^3 - 5 * x^2 + 8 * x - 4 is non-negative for every x ∈ [1, ∞)
    have h1 : x ≥ 1 := by
      simpa using hx
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x ^ 2 - 2 * x + 1), sq_nonneg ((x - 2) * (x - 1))]
  · -- Show that 8 is the least element of the set
    constructor
    · -- Show 8 is in the set
      use 2, 2
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals norm_num
    · -- Show no smaller element is in the set
      intro y hy
      rcases hy with ⟨a, b, ha, hb, heq⟩
      have ha1 : a ≥ 1 := by
        simpa using ha
      have hb1 : b ≥ 1 := by
        simpa using hb
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a * b - 4), sq_nonneg (a - b), sq_nonneg (a * (a - 2)), sq_nonneg (b * (b - 2)), mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ b - 1 by linarith), mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ (a - 1 : ℝ) by linarith), mul_nonneg (show (0 : ℝ) ≤ b - 1 by linarith) (show (0 : ℝ) ≤ (b - 1 : ℝ) by linarith)]