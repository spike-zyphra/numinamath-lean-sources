import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_297524 :
  IsLeast {x | ∃ a b : ℝ, a ≥ 1 / 2 ∧ b ≥ 1 / 2 ∧
    x = a ^ 3 + b ^ 3 + a ^ 2 * b + a * b ^ 2 - 3 * (a ^ 2 + b ^ 2 + a * b) + 3 * (a + b)} 1 := by
  constructor
  · -- First, prove that 1 is in the set.
    use 1, 1
    norm_num
  · -- Then, show that for all x in the set, 1 ≤ x
    rintro x ⟨a, b, ha, hb, hx⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a - 1), sq_nonneg (b - 1),
      sq_nonneg (a - b), sq_nonneg (a + b - 2),
      mul_nonneg (show (0 : ℝ) ≤ a - 1 / 2 by linarith) (show (0 : ℝ) ≤ b - 1 / 2 by linarith)
    ]