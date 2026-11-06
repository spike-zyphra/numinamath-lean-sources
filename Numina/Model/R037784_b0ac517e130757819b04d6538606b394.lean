import Mathlib

theorem number_theory_123278 : ∃ n : ℕ, 0 < n ∧ (3^n) % (2^n) > 10^2021 := by
  use 13983
  constructor
  · norm_num
  · native_decide