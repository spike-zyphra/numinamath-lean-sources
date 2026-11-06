import Mathlib

theorem algebra_79290 {f : Polynomial ℚ} (hf : f.degree = 3)
    (hfg : ∃ x, f.eval x = 0 ∧ f.derivative.eval x = 0) :
    ∀ r ∈ f.roots, ∃ q : ℚ, r = q := by
  intro r hr
  refine ⟨r, rfl⟩