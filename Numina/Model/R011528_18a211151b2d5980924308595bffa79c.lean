import Mathlib

theorem number_theory_3428 : (Nat.factorial 5364) % 10^1337 = 0 ∧ (Nat.factorial 5364) % 10^1338 ≠ 0 := by 
  native_decide