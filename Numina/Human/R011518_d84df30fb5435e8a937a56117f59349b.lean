import Mathlib

/-Find the number of divisors of 2^9 * 3^14-/

theorem number_theory_257019: (Nat.divisors (2^9*3^14)).card = 150 := by

  -- we use the powerful hypothesis in lean4 to prove this
  rw [Nat.card_divisors]
  native_decide
  norm_num