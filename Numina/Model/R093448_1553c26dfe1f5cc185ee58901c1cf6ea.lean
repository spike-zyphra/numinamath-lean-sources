import Mathlib

theorem algebra_320164 (f : ℝ → ℝ) (hf : f = fun x => x^2 - 31 * x + 220 - 2^x * (31 - 2 * x - 2^x)) :
    ∃ x1 x2, x1 ≠ x2 ∧ f x1 = 0 ∧ f x2 = 0 ∧ x1^2 + x2^2 = 25 := by
  use 3, 4
  constructor
  · norm_num
  constructor
  · -- Show that f 3 = 0
    rw [hf]
    norm_num
  constructor
  · -- Show that f 4 = 0
    rw [hf]
    norm_num
  · norm_num