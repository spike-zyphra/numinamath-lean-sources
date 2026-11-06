import Mathlib

theorem number_theory_239519: {n: ℕ | (1 ≤ n) ∧ (n ≤ 6) ∧ (∃ a b c: ℤ, a ^ n + b ^ n = c ^ n + n)} = {1, 2, 3} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First prove {n: ℕ | (1 ≤ n) ∧ (n ≤ 6) ∧ (∃ a b c: ℤ, a ^ n + b ^ n = c ^ n + n)} ⊆ {1, 2, 3}
    rintro ⟨h1, h6, ⟨a, b, c, he⟩⟩
    have h4 : n ≥ 1 := h1
    have h5 : n ≤ 6 := h6
    have h7 : n < 7 := by omega
    have h8 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
      interval_cases n <;> omega
    rcases h8 with (r | r | r | r | r | r)
    · -- n = 1
      omega
    · -- n = 2
      omega
    · -- n = 3
      omega
    · -- n = 4
      rw [r] at he
      exfalso
      have eq : a ^ 4 + b ^ 4 = c ^ 4 + 4 := he
      have eq1 : a ^ 4 % 8 = 0 ∨ a ^ 4 % 8 = 1 := by
        have h1 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have eq2 : b ^ 4 % 8 = 0 ∨ b ^ 4 % 8 = 1 := by
        have h1 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have eq3 : c ^ 4 % 8 = 0 ∨ c ^ 4 % 8 = 1 := by
        have h1 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      omega
    · -- n = 5
      rw [r] at he
      exfalso
      have eq : a ^ 5 + b ^ 5 = c ^ 5 + 5 := he
      have eq1 : a ^ 5 % 11 = 0 ∨ a ^ 5 % 11 = 1 ∨ a ^ 5 % 11 = 10 := by
        have h1 : a % 11 = 0 ∨ a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have eq2 : b ^ 5 % 11 = 0 ∨ b ^ 5 % 11 = 1 ∨ b ^ 5 % 11 = 10 := by
        have h1 : b % 11 = 0 ∨ b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have eq3 : c ^ 5 % 11 = 0 ∨ c ^ 5 % 11 = 1 ∨ c ^ 5 % 11 = 10 := by
        have h1 : c % 11 = 0 ∨ c % 11 = 1 ∨ c % 11 = 2 ∨ c % 11 = 3 ∨ c % 11 = 4 ∨ c % 11 = 5 ∨ c % 11 = 6 ∨ c % 11 = 7 ∨ c % 11 = 8 ∨ c % 11 = 9 ∨ c % 11 = 10 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      omega
    · -- n = 6
      rw [r] at he
      exfalso
      have eq : a ^ 6 + b ^ 6 = c ^ 6 + 6 := he
      have eq1 : a ^ 6 % 13 = 0 ∨ a ^ 6 % 13 = 1 ∨ a ^ 6 % 13 = 12 := by
        have h1 : a % 13 = 0 ∨ a % 13 = 1 ∨ a % 13 = 2 ∨ a % 13 = 3 ∨ a % 13 = 4 ∨ a % 13 = 5 ∨ a % 13 = 6 ∨ a % 13 = 7 ∨ a % 13 = 8 ∨ a % 13 = 9 ∨ a % 13 = 10 ∨ a % 13 = 11 ∨ a % 13 = 12 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have eq2 : b ^ 6 % 13 = 0 ∨ b ^ 6 % 13 = 1 ∨ b ^ 6 % 13 = 12 := by
        have h1 : b % 13 = 0 ∨ b % 13 = 1 ∨ b % 13 = 2 ∨ b % 13 = 3 ∨ b % 13 = 4 ∨ b % 13 = 5 ∨ b % 13 = 6 ∨ b % 13 = 7 ∨ b % 13 = 8 ∨ b % 13 = 9 ∨ b % 13 = 10 ∨ b % 13 = 11 ∨ b % 13 = 12 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have eq3 : c ^ 6 % 13 = 0 ∨ c ^ 6 % 13 = 1 ∨ c ^ 6 % 13 = 12 := by
        have h1 : c % 13 = 0 ∨ c % 13 = 1 ∨ c % 13 = 2 ∨ c % 13 = 3 ∨ c % 13 = 4 ∨ c % 13 = 5 ∨ c % 13 = 6 ∨ c % 13 = 7 ∨ c % 13 = 8 ∨ c % 13 = 9 ∨ c % 13 = 10 ∨ c % 13 = 11 ∨ c % 13 = 12 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      omega
  · -- Now prove {1, 2, 3} ⊆ {n: ℕ | (1 ≤ n) ∧ (n ≤ 6) ∧ (∃ a b c: ℤ, a ^ n + b ^ n = c ^ n + n)}
    rintro (h | h | h)
    · -- n = 1
      rw [h]
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show that there is a solution
        use 1, 0, 0
        all_goals norm_num
    · -- n = 2
      rw [h]
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show that there is a solution
        use 1, 1, 0
        all_goals norm_num
    · -- n = 3
      rw [h]
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show that there is a solution
        use 1, 1, -1
        all_goals norm_num