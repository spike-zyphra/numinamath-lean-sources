import Mathlib

theorem algebra_225439 {f g : ℝ → ℝ} (hf : f = fun x => x ^ 2 - x + 1)
    (hg : g = fun x => -x ^ 2 + x + 1) :
    ∃ h : ℝ → ℝ, (∀ x, h x = (x - 1) ^ 2) ∧
    (∀ x, h (f x) = h (g x)) := by 
  use fun x => (x - 1) ^ 2
  constructor
  · -- Show h x = (x - 1) ^ 2
    intro x
    rfl
  · -- Show h (f x) = h (g x)
    intro x
    simp [hf, hg]
    <;> ring