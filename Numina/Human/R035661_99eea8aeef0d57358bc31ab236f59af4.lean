import Mathlib

/- The least common multiple of two integers is 240, and the greatest common divisor is 24. Given that one of the integers is 48, what is the other integer? -/
theorem algebra_21752 {x y : ℕ} (hxy1 : Nat.lcm x y = 240) (hxy2 : Nat.gcd x y = 24)
    (hx : x = 48) : y = 120 := by
  -- We shall use the fact that x * y = gcd (x, y) * lcm (x, y), which is must faster than the given solution.
  have h' := Nat.gcd_mul_lcm x y
  rw [hxy1, hxy2, hx] at h'
  omega
