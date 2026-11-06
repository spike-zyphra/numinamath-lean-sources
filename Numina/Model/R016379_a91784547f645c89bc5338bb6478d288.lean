import Mathlib

theorem number_theory_74848 (n : ℕ) :
    ∃ a b, a ≠ b ∧ (Nat.digits 10 (n ^ a + 1)).length = (Nat.digits 10 (n ^ b + 1)).length ∧
      List.reverse (Nat.digits 10 (n ^ a + 1)) = Nat.digits 10 (n ^ b + 1) ↔ n = 3 := by
  by_cases h1 : n = 0
  · -- Assume n = 0, prove that the statement is equivalent to n = 3 (which is 0 = 3, false)
    use 0, 0
    simp at *
    all_goals omega
  · -- n ≠ 0
    by_cases h2 : n = 1
    · -- Assume n = 1, prove that the statement is equivalent to n = 3 (which is 1 = 3, false)
      use 0, 0
      simp at *
      all_goals omega
    · -- n ≠ 0, n ≠ 1
      by_cases h3 : n = 3
      · -- Assume n = 3, prove that the statement is equivalent to n = 3 (which is true)
        use 3, 4
        simp [h3] at *
        all_goals
          try { tauto }
          <;> try { aesop }
          <;> try { norm_num at h3 ⊢ }
          <;> try { all_goals omega }
      · -- n ≠ 0, n ≠ 1, n ≠ 3
        use 0, 0
        simp at *
        all_goals omega