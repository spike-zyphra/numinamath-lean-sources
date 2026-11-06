import Mathlib

open Real

theorem inequalities_6511 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    x^2 < x ∧ (x^2 < x ↔ 0 < x ∧ x < 1) ∧ (x^2 > x → x > 1) := by
  constructor
  · -- Show x^2 < x
    nlinarith
  constructor
  · -- Show x^2 < x ↔ 0 < x ∧ x < 1
    constructor
    · -- Assume x ^ 2 < x, prove 0 < x ∧ x < 1
      intro h
      exact hx
    · -- Assume 0 < x ∧ x < 1, prove x ^ 2 < x
      rintro ⟨hx1, hx2⟩
      nlinarith
  · -- Show x^2 > x → x > 1
    intro h
    nlinarith