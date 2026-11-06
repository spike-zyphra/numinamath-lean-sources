import Mathlib

theorem number_theory_179519 : (30 * 17) % (Nat.minFac (3^11 + 5^13)) = 0 := by
  have h1 : Nat.minFac (3^11 + 5^13) = 2 := by 
    native_decide
  calc 
    (30 * 17) % (Nat.minFac (3^11 + 5^13)) = (30 * 17) % 2 := by 
      rw [h1]
    _ = 510 % 2 := by 
      norm_num
    _ = 0 := by 
      norm_num