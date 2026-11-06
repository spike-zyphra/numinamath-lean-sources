import Mathlib

/- What is the product of the least common multiple and the greatest common factor of 22 and 48? -/
theorem algebra_18736 {x y : ℕ} (hx : x = 22) (hy : y = 48) :
    Nat.lcm x y * Nat.gcd x y = 1056 := by 
  subst_vars; rfl