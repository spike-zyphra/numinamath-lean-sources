import Mathlib

/-
A random number generator will always output 7 . Sam uses this random number generator once. What is the expected value of the output?
-/
theorem algebra_609668  (f : ℕ → ℝ) (hf : ∀ x, f x = if x = 7 then (1 / 1) else 0) : 7 * (1 / 1) + 0 * (0 / 1) = 7 := by

  norm_num [hf]