import Mathlib

open Real Int Nat Set
open scoped BigOperators

theorem inequalities_287088 (x : ℝ) :
  4 * ⌊x⌋^2 - 36 * ⌊x⌋ + 45 ≤ 0 ↔ 2 ≤ ⌊x⌋ ∧ ⌊x⌋ < 8 := by
  constructor
  · -- Prove the forward direction: given the inequality, derive the bounds on ⌊x⌋.
    intro h
    constructor
    · -- First, show that 2 ≤ ⌊x⌋.
      nlinarith
    · -- Then show that ⌊x⌋ < 8.
      nlinarith
  · -- Prove the reverse direction: given the bounds on ⌊x⌋, show the inequality holds.
    rintro ⟨h1, h2⟩
    have h3 : ⌊x⌋ ≤ 7 := by
      omega
    have h4 : ⌊x⌋ = 2 ∨ ⌊x⌋ = 3 ∨ ⌊x⌋ = 4 ∨ ⌊x⌋ = 5 ∨ ⌊x⌋ = 6 ∨ ⌊x⌋ = 7 := by 
      omega
    rcases h4 with (h | h | h | h | h | h)
    · -- Case ⌊x⌋ = 2
      rw [h]
      norm_num
    · -- Case ⌊x⌋ = 3
      rw [h]
      norm_num
    · -- Case ⌊x⌋ = 4
      rw [h]
      norm_num
    · -- Case ⌊x⌋ = 5
      rw [h]
      norm_num
    · -- Case ⌊x⌋ = 6
      rw [h]
      norm_num
    · -- Case ⌊x⌋ = 7
      rw [h]
      norm_num