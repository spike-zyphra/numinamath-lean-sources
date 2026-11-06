import Mathlib

theorem algebra_16871 {x y : ℕ} (hx : x = 100) (hy : y = 120) :
    Nat.gcd x y * Nat.lcm x y = 12000 := by 
  rw [hx, hy]
  norm_num [Nat.gcd, Nat.lcm]