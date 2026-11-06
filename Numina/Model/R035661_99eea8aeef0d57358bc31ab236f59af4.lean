import Mathlib

theorem algebra_21752 {x y : ℕ} (hxy1 : Nat.lcm x y = 240) (hxy2 : Nat.gcd x y = 24)
    (hx : x = 48) : y = 120 := by 
  rw [hx] at hxy1 hxy2
  have key := Nat.gcd_mul_lcm 48 y 
  rw [hxy1, hxy2] at key 
  nlinarith