import Mathlib

theorem algebra_9454 (a : ℝ) :
  (∀ x : ℝ, x^2 - a * x + a > 0) ↔ 0 < a ∧ a < 4 := by
  constructor
  · -- Assume the inequality is always satisfied, prove 0 < a ∧ a < 4
    intro h
    have h1 := h 0
    have ha1 : 0 < a := by nlinarith
    have h2 := h 2
    have ha2 : a < 4 := by nlinarith
    constructor
    · exact ha1
    · exact ha2
  · -- Assume 0 < a ∧ a < 4, prove the inequality is always satisfied
    rintro ⟨ha1, ha2⟩
    intro x
    have h1 : x^2 - a * x + a > 0 := by
      nlinarith [sq_nonneg (x - a / 2), sq_pos_of_pos (show 0 < a by linarith), sq_nonneg (a - 2)]
    exact h1