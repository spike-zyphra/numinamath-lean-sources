import Mathlib

def is_perfect_pair (x y : ℕ) := ∃ m n, x + y = m^2 ∧ x * y = n^2

theorem number_theory_249605 : ∃ x, is_perfect_pair 122 x := by
  use 122 * 121
  refine ⟨122, 122 * 11, by norm_num, by norm_num⟩