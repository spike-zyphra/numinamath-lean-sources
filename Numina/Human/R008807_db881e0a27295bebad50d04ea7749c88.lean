import Mathlib

/-
Find a multiple of 11 that leaves a remainder of 1 when divided by each of the integers 2, 3, 5, and 7.
-/
theorem number_theory_4705 {n : ℤ} : n = 2101 →
    n ≡ 0 [ZMOD 11] ∧ n ≡ 1 [ZMOD 2] ∧
    n ≡ 1 [ZMOD 3] ∧ n ≡ 1 [ZMOD 5] ∧
    n ≡ 1 [ZMOD 7] := by
  -- `2101` is exactly a solution, as we can check.
  intro hn
  subst hn
  aesop
