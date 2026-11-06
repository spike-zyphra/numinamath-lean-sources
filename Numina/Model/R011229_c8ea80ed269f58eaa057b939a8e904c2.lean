import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_229237 : IsGreatest {a : ℝ | ∀ x ∈ Set.Icc 0 1, |a * x^2 - a * x + 1| ≤ 1} 8 := by
  constructor
  · -- Show 8 is in the set
    show ∀ x ∈ Set.Icc 0 1, |8 * x^2 - 8 * x + 1| ≤ 1
    intro x h
    rcases h with ⟨hx0, hx1⟩
    have h1 : -1 ≤ 8 * x^2 - 8 * x + 1 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have h2 : 8 * x^2 - 8 * x + 1 ≤ 1 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    apply abs_le.mpr
    constructor
    · linarith [h1]
    · linarith [h2]
  · -- Show 8 is greatest in the set
    intro a ha
    have h3 := ha (1 / 2 : ℝ) (by norm_num [Set.mem_Icc])
    have h4 : -1 ≤ a * (1 / 2 : ℝ) ^2 - a * (1 / 2) + 1 := by
      linarith [abs_le.mp h3]
    have h5 : a * (1 / 2 : ℝ) ^ 2 - a * (1 / 2) + 1 ≤ 1 := by
      linarith [abs_le.mp h3]
    nlinarith