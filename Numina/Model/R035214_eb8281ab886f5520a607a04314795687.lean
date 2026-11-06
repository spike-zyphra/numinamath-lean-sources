import Mathlib

theorem algebra_9336 {f g : ℝ → ℝ} (hf : ∀ x, x ≥ 0 → f x = x ^ 2 - 2 * x)(hg : ∀ x, x < 0 → f x = g x) (hodd : Function.Odd f) : ∀x, x < 0 → g x = -x ^ 2 - 2 * x := by
  intro x hx
  have h1 : -x ≥ 0 := by linarith
  have h2 : f (-x) = (-x) ^ 2 - 2 * (-x) := hf (-x) (show -x ≥ 0 by linarith)
  have h3 : f (-x) = - f x := by 
    apply hodd
  have h4 : f x = g x := by 
    apply hg x hx
  have h5 : g x = -x ^ 2 - 2 * x := by
    have eq1 : f (-x) = x ^ 2 + 2 * x := by 
      rw [h2]
      ring
    have eq2 : f (-x) = -f x := h3
    have eq3 : f x = g x := h4
    rw [eq3] at eq2
    linarith [eq1, eq2]
  exact h5