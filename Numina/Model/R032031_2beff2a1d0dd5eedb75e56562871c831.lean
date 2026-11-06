import Mathlib

theorem number_theory_249802 (n : ℕ) :
    ∃ a b, n ∣ 4 * a ^ 2 + 9 * b ^ 2 - 1 := by
  use 0
  use 0
  simp
  <;> norm_num
  <;> tauto