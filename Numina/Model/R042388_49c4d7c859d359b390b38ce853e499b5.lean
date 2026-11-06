import Mathlib

theorem number_theory_118523 : (Nat.Prime 1163) ∧ ¬(Nat.Prime 16424) := by
  constructor
  · -- Prove that 1163 is prime
    norm_num
  · -- Prove that 16424 is not prime
    norm_num
    all_goals try { norm_num }