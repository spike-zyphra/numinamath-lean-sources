import Mathlib

theorem number_theory_122656 : (Nat.divisors 24).card = 8 ∧ (Nat.divisors 140).card = 12 ∧ (Nat.divisors (2012^2013)).card = 8110378 := by
  constructor
  · -- Show that 24 has 8 divisors.
    native_decide
  constructor
  · -- Show that 140 has 12 divisors.
    native_decide
  · -- Show that 2012^2013 has 8110378 divisors.
    have h1 : (Nat.divisors (2012 ^ 2013)).card = 8110378 := by 
      have h2 : (2012 ^ 2013 : ℕ) ≠ 0 := by 
        norm_num 
      rw [Nat.card_divisors (h2)]
      have h3 : (2012 ^ 2013 : ℕ) = 2 ^ 4026 * 503 ^ 2013 := by 
        ring_nf 
      rw [h3] 
      native_decide 
    exact h1