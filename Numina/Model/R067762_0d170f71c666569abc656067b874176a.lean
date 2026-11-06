import Mathlib

theorem number_theory_139153 (m n : ℤ) (hm : m > 0) (hn : n > 0) :
    19 ∣ 11*m + 2*n ↔ 19 ∣ 18*m + 5*n := by
  constructor
  · -- Assume 19 divides 11m + 2n, prove 19 divides 18m + 5n
    intro h
    omega
  · -- Assume 19 divides 18m + 5n, prove 19 divides 11m + 2n
    intro h
    omega