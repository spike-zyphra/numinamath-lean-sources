import Mathlib

theorem algebra_18800 (x : ℕ) : 10^x - 10 = 9990 ↔ x = 4 := by
  constructor
  · -- Assume $10^x - 10 = 9990$, and prove $x = 4$
    intro h
    have h1 : 10 ^ x ≥ 10 := by omega
    have h2 : 10 ^ x = 10000 := by omega
    have h3 : x = 4 := by
      have h4 : 10 ^ x = 10 ^ 4 := by
        norm_num [h2]
      have h5 : x = 4 := by
        exact Nat.pow_right_injective (by norm_num) h4
      exact h5
    exact h3
  · -- Assume $x = 4$, and prove $10^x - 10 = 9990$
    intro h
    rw [h]
    all_goals norm_num