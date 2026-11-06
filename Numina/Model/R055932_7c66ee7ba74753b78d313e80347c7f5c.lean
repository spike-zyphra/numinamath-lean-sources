import Mathlib

theorem algebra_265611 (E : ℝ → ℝ → ℝ) (hE : E = fun x y => 2 * x ^ 2 + 4 * x * y + 5 * y ^ 2 - 22)
    (l : ℝ → ℝ → ℝ) (hl : l = fun x y => x - y + 1) :
    ∃ E' : ℝ → ℝ → ℝ, E' = fun x y => 5 * x ^ 2 + 4 * x * y + 2 * y ^ 2 + 6 * x - 19 := by
  refine' ⟨fun x y => 5 * x ^ 2 + 4 * x * y + 2 * y ^ 2 + 6 * x - 19, rfl⟩