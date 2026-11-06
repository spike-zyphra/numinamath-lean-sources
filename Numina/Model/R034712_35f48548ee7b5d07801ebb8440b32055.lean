import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_116849 (a : ℝ) :
  (3 - a) * (3 + 2*a - 1)^2 * (3 - 3*a) ≤ 0 ↔ a = -1 ∨ 1 ≤ a ∧ a ≤ 3 := by
  constructor
  · -- Forward implication: If the inequality holds, then a = -1 or 1 ≤ a ≤ 3
    intro h
    have h1 : (3 + 2 * a - 1) ^ 2 ≥ 0 := by nlinarith
    by_cases h2 : (3 + 2 * a - 1) ^ 2 > 0
    · -- If (3 + 2*a - 1) ^ 2 > 0, then (3 - a) * (3 - 3*a) ≤ 0 must hold
      have h3 : (3 - a) * (3 - 3 * a) ≤ 0 := by
        nlinarith
      have h4 : 1 ≤ a ∧ a ≤ 3 := by
        constructor
        · -- Proof for 1 ≤ a
          nlinarith
        · -- Proof for a ≤ 3
          nlinarith
      right
      exact h4
    · -- Case where (3 + 2*a - 1) ^ 2 = 0
      have h2' : (3 + 2 * a - 1) ^ 2 = 0 := by linarith
      have h3 : (3 + 2 * a - 1) = 0 := by
        apply pow_eq_zero 
        exact h2'
      have h4 : a = -1 := by
        nlinarith 
      left 
      linarith 
  · -- Backward implication: If a = -1 or 1 ≤ a ≤ 3, then the inequality holds
    rintro (h | ⟨h1, h2⟩)
    · -- Case where a = -1
      rw [h]
      norm_num
    · -- Case where 1 ≤ a ≤ 3
      have h3 : (3 - a) * (3 - 3 * a) ≤ 0 := by
        nlinarith
      have h4 : (3 + 2 * a - 1) ^ 2 ≥ 0 := by nlinarith
      nlinarith