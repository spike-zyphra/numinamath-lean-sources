import Mathlib

theorem number_theory_213552 :
    ∃ a b c d : ℕ, a^3 + b^3 + c^3 + d^3 = 100^100 := by
  use 100 ^ 33, 2 * 100 ^ 33, 3 * 100 ^ 33, 4 * 100 ^ 33
  norm_num
  <;> ring_nf
  <;> norm_num