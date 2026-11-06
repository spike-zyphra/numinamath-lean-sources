import Mathlib

open Real

theorem algebra_134536 {f g : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = -g x) :
    ∀ x, f (g x) + g (f x) = f (g (-x)) + g (f (-x)) := by
  intro x
  have h1 : f (g (-x)) = f (g x) := by
    have h2 : g (-x) = - (g x) := by
      specialize hg x
      linarith
    rw [h2]
    have h3 : f (- (g x)) = f (g x) := by
      specialize hf (g x)
      simpa using hf
    linarith
  have h2 : g (f (-x)) = g (f x) := by
    have h3 : f (-x) = f x := by
      specialize hf x
      linarith
    rw [h3]
  -- Now, we can rewrite the right side of the equation
  rw [h1, h2]
  all_goals linarith