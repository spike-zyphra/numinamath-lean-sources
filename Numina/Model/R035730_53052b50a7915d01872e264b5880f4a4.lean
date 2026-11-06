import Mathlib

theorem number_theory_57786 :
    ∃ k : ℕ, 0 < k ∧ Nat.gcd 2012 2020 = Nat.gcd (2012 + k) 2020 ∧
      Nat.gcd (2012 + k) 2020 = Nat.gcd 2012 (2020 + k) ∧
      Nat.gcd 2012 (2020 + k) = Nat.gcd (2012 + k) (2020 + k) := by
  use 32
  constructor
  · norm_num
  constructor
  · -- Show that gcd(2012, 2020) = gcd(2012 + 32, 2020)
    norm_num
  constructor
  · -- Show that gcd(2012 + 32, 2020) = gcd(2012, 2020 + 32)
    norm_num
  · -- Show that gcd(2012, 2020 + 32) = gcd(2012 + 32, 2020 + 32)
    norm_num