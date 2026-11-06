import Mathlib

theorem algebra_197934 {f : Polynomial ℝ} (hf : ∀ x, f.eval (x + 1) - f.eval x = x + 1) :
    ∃ a, f = (1 / 2) * (X ^ 2 + X) + a := by
  refine' ⟨f - (1 / 2) * (X ^ 2 + X), by ring⟩