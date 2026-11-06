import Mathlib

theorem algebra_189027 (a : ℝ) :
    ∃ p q, a^2 + a * p + q = 0 ↔ ∃ x, p^2 - 4 * q = 0 ∧ a = x := by 
  use -2 * a
  use a ^ 2
  constructor
  · -- Assume left side is true, prove right side
    intro h
    exact ⟨a, by nlinarith, rfl⟩
  · -- Assume right side is true, prove left side
    rintro ⟨x, hx1, hx2⟩
    nlinarith