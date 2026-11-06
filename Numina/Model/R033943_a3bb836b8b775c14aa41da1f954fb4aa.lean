import Mathlib

theorem algebra_9119 : 
  let even (f : ℝ → ℝ) := ∀ x, f x = f (-x)
  let odd (f : ℝ → ℝ) := ∀ x, f x = - f (-x)
  (¬ (∀ f : ℝ → ℝ, even f ∨ odd f)) ↔ (∃ f : ℝ → ℝ , (¬ even f) ∧ (¬ odd f)) := by
  apply not_forall.trans
  simp