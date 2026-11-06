import Mathlib

theorem algebra_16645 (a b c : ℝ) (f : ℝ → ℝ) (hf : f = fun x => 2*x^2 - x + 7)
    (h : ∀ x, f (x - 4) = a*x^2 + b*x + c) :
    a + b + c = 28 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  simp [hf] at eq1 eq2 eq3
  ring_nf at eq1 eq2 eq3
  linarith