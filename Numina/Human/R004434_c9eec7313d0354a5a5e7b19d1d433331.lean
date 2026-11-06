import Mathlib

theorem algebra_265930 {f : Polynomial ℝ} (hf0 : f.eval 0 = 1)
    (hfn : ∀ x y : ℝ, f.eval (x - y) + f.eval x ≥ (2 * x ^ 2 - 2 * x * y + y ^ 2) + 2 * x - y + 2) :
    ∀ x : ℝ, f.eval x ≥ x ^ 2 + x + 1 := by
  intro x
  have := hfn x 0
  simp [pow_two] at this
  linarith