import Mathlib

theorem number_theory_604559 :
    ∃ n : ℕ, 0 < n ∧ (3^n % 2^n) > 10^2021 := by
  use 10000
  constructor
  · -- Show n is positive
    norm_num
  · -- Show 3^n % 2^n > 10^2021
    native_decide