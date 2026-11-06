import Mathlib

theorem number_theory_148040 {a b : ℕ} (ha : 0 < a) (hb : b ≠ 0) :
    ∃ q r : ℕ, 0 ≤ r ∧ r < b ∧ a = b * q + r := by
  use a / b
  use a % b
  constructor
  · -- Show 0 ≤ r
    omega
  constructor
  · -- Show r < b
    have h1 : a % b < b := by
      apply Nat.mod_lt
      all_goals
      try { 
        omega 
      }
    omega
  · -- Show a = b * q + r
    have h2 : a = b * (a / b) + (a % b) := by
      rw [Nat.div_add_mod]
    omega