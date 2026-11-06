import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_294217 :
  IsGreatest {x : ℝ | ∃ a b, x = (a + 2 * b) / (2 * a + b) ∧
    a + b - 2 ≥ 0 ∧ b - a - 1 ≤ 0 ∧ a ≤ 1} (7 / 5) := by
  constructor
  · -- First, prove that 7/5 is in the set
    use 1 / 2, 3 / 2
    norm_num
  · -- Now prove that for all x in the set, x ≤ 7/5
    intro x hx
    rcases hx with ⟨a, b, h_eq, h1, h2, h3⟩
    have h4 : 2 * a + b > 0 := by
      nlinarith
    have h_eq' : (a + 2 * b) / (2 * a + b) ≤ 7 / 5 := by
      apply (div_le_iff₀ h4).mpr
      nlinarith
    linarith [h_eq, h_eq']