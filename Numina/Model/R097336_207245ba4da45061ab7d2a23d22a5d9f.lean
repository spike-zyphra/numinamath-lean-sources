import Mathlib

theorem algebra_244504 (f g : ℝ → ℝ) (hf : f = fun x => x^2) (hg : g = fun x => 2 * x^2) :
    ∃ k, ∀ x, g x = k * f x := by
  use 2
  intro x
  rw [hg, hf]
  all_goals simp
  <;> ring