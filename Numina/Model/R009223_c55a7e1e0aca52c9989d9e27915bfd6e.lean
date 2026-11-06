import Mathlib

theorem number_theory_15746 : ((Nat.divisors 3240).filter fun n => 3 ∣ n).card = 32 := by
  native_decide