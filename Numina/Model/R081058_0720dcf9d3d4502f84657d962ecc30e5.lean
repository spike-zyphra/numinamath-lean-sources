import Mathlib

theorem number_theory_4310 {x y : ℕ} (hx : x > 0) (hy : y > 0) (h_lcm : Nat.lcm x y = 360) (h_gcd : Nat.gcd x y = 60) :
    x * y = 21600 := by
  have h : x.gcd y * x.lcm y = x * y := by
    rw [Nat.gcd_mul_lcm]
  rw [h_lcm, h_gcd] at h
  linarith