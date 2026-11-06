import Mathlib

open Real

theorem algebra_121292 {f g : ℝ → ℝ} (hg : g = fun x => logb 2 x) (hfg : ∀ x, f (-x) = -g x) :
    ∀ x, x < 0 → f x = -logb 2 (-x) := by
  intro x hx
  have h1 : f x = -g (-x) := by
    specialize hfg (-x)
    simp at hfg ⊢
    linarith
  rw [h1]
  simp [hg]
  <;> try tauto