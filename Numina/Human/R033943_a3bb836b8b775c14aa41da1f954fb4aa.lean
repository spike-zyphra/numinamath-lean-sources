import Mathlib

/- Write the negation of the proposition "Every function has parity". -/
theorem algebra_9119 : 
  let even (f : ℝ → ℝ) := ∀ x, f x = f (-x)
  let odd (f : ℝ → ℝ) := ∀ x, f x = - f (-x)
  (¬ (∀ f : ℝ → ℝ, even f ∨ odd f)) ↔ (∃ f : ℝ → ℝ , (¬ even f) ∧ (¬ odd f)) := by
  -- this is just the opposite statement of the original statement.
  simp only [not_forall, not_or]