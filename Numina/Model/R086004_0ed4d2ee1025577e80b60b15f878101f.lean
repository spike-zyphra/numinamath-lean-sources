import Mathlib

open Real Int Nat Set
open scoped BigOperators

theorem inequalities_12350 (x : ℝ) :
  4 * ⌊x⌋^2 - 36 * ⌊x⌋ + 45 ≤ 0 ↔ ⌊x⌋ ∈ Ico 2 8 := by
    simp only [mem_Ico]
    constructor
    · -- Assume 4 * ⌊x⌋^2 - 36 * ⌊x⌋ + 45 ≤ 0, prove 2 ≤ ⌊x⌋ < 8
      intro h
      have h1 : ⌊x⌋ ≥ 2 := by nlinarith
      have h2 : ⌊x⌋ < 8 := by nlinarith
      exact ⟨h1, h2⟩
    · -- Assume ⌊x⌋ ∈ Ico 2 8, prove 4 * ⌊x⌋^2 - 36 * ⌊x⌋ + 45 ≤ 0
      rintro ⟨h1, h2⟩
      have h3 : ⌊x⌋ ≥ 2 := by linarith
      have h4 : ⌊x⌋ < 8 := by linarith
      interval_cases h : ⌊x⌋ <;> omega