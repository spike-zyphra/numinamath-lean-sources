import Mathlib

/- What is the units digit of $7^{2009}$ ?-/
theorem number_theory_608399 : (7 ^ 2009) % 10 = 7 := by
  -- Note that 7⁴ % 10 = 1.
  rw [show 2009 = 4 * 502 + 1 by norm_num, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num