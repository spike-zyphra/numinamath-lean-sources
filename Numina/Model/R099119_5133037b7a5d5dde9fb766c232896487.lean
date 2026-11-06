import Mathlib

theorem algebra_13217 {f g h : ℝ → ℝ}
    (hf : f = fun x => -3 * x ^ 2 + x - 4)
    (hg : g = fun x => -5 * x ^ 2 + 3 * x - 8)
    (hh : h = fun x => 5 * x ^ 2 + 5 * x + 1) :
    ∀ x, f x + g x + h x = -3 * x ^ 2 + 9 * x - 11 := by 
  intro x 
  rw [hf, hg, hh]
  ring