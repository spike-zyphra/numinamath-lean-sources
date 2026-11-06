import Mathlib

theorem combinatorics_95105 : 
  Nat.multinomial {1,2,3,4,5,6,7,8} 2 = Nat.factorial 16 / 2^8 := by
  native_decide