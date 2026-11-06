import Mathlib

theorem algebra_14876 : Nat.choose 12 5 * Nat.factorial 5 = 95040 := by 
  calc 
    Nat.choose 12 5 * Nat.factorial 5 = 792 * 120 := by rfl 
    _ = 95040 := by norm_num