import Mathlib

-- How many natural divisors does 121 have? How many natural divisors does 1000 have? How many natural divisors does 1000000000 have?
theorem number_theory_110942 :
    (121 : ℕ).divisors.card = 3 ∧
    (1000 : ℕ).divisors.card = 16 ∧
    (1000000000 : ℕ).divisors.card = 100 := by
  constructor
  · -- Show that 121 has 3 divisors.
    have h1 : (121 : ℕ).divisors.card = 3 := by
      native_decide
    exact h1
  constructor
  · -- Show that 1000 has 16 divisors.
    have h1 : (1000 : ℕ).divisors.card = 16 := by
      native_decide
    exact h1
  · -- Show that 1000000000 has 100 divisors.
    have h1 : (1000000000 : ℕ).divisors.card = 100 := by
      have h1 : (1000000000 : ℕ).divisors.card = 100 := by
        rw [Nat.card_divisors]
        all_goals try { native_decide }
      exact h1
    exact h1