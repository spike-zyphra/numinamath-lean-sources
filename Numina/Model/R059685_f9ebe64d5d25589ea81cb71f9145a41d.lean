import Mathlib

theorem number_theory_36104 (n : ℕ) : 11 ∣ n ^ 11 - n := by
  have h1 : n ^ 11 % 11 = n % 11 := by
    have h2 : n ^ 11 % 11 = (n % 11) ^ 11 % 11 := by
      rw [Nat.pow_mod]
    rw [h2]
    have h3 : (n % 11) ^ 11 % 11 = n % 11 := by
      have h4 : n % 11 < 11 := by
        omega
      interval_cases h5 : n % 11 <;> norm_num at *
      all_goals
        try { tauto }
        <;> try { try { trivial } }
        <;> try { try { omega } }
        <;> try { tauto }
    exact h3
  omega