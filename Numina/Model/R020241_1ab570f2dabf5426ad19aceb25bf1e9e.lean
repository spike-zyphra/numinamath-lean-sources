import Mathlib

theorem number_theory_113604 (a b : ℕ) :
    a.gcd b * a.lcm b = a * b := by 
  rw [Nat.gcd_mul_lcm]