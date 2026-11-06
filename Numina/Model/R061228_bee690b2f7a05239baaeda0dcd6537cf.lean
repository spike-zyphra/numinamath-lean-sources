import Mathlib

theorem algebra_215396 (f g : ℝ → ℝ) (hf : f = fun x => x^2) (hg : g = fun x => 2 * x^2) :
    ∃ c, ∀ x, g x = c * f x := by 
  use 2
  intro x
  rw [hg, hf]
  all_goals ring