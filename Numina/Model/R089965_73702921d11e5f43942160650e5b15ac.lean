import Mathlib

theorem algebra_12236 : ∑ x in (315 : ℕ).primeFactors, x = 15 := by
  native_decide  -- automatically handles concrete arithmetic