import Mathlib

theorem number_theory_318374 (d n : ℕ) (hd : d > 0) (hne : d ≠ 2)
    (hne1 : d ≠ 32 * n ^ 2 - 40 * n + 13) (hne2 : d ≠ 32 * n ^ 2 - 24 * n + 5) :
    ∃ a b, (a = 2 ∧ b = 32 * n ^ 2 - 40 * n + 13) ∨
    (a = 2 ∧ b = 32 * n ^ 2 - 24 * n + 5) ∨
    (a = 32 * n ^ 2 - 40 * n + 13 ∧ b = 32 * n ^ 2 - 24 * n + 5) ∧
    ¬ ∃ m, m ^ 2 = a * b - 1 := by
  use 2, 32 * n ^ 2 - 40 * n + 13
  left
  constructor
  · rfl
  · rfl