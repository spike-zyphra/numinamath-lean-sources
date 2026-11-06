import Mathlib

set_option maxHeartbeats 10000000

theorem number_theory_4863 :
    (Nat.totient 100 = 40) ∧
    (Nat.totient 256 = 128) ∧
    (Nat.totient 1001 = 720) ∧
    (Nat.totient (2*3*5*7*11*13) = 5760) ∧
    (Nat.totient (Nat.factorial 10) = 829440) ∧
    (Nat.totient (Nat.factorial 20) = 416084687585280000):= by
  constructor
  · -- Show Nat.totient 100 = 40
    native_decide
  constructor
  · -- Show Nat.totient 256 = 128
    native_decide
  constructor
  · -- Show Nat.totient 1001 = 720
    native_decide
  constructor
  · -- Show Nat.totient (2*3*5*7*11*13) = 5760
    native_decide
  constructor
  · -- Show Nat.totient (Nat.factorial 10) = 829440
    native_decide
  · -- Show Nat.totient (Nat.factorial 20) = 416084687585280000
    rw [Nat.totient_eq_div_primeFactors_mul]
    native_decide
    all_goals native_decide