import Mathlib

theorem number_theory_71902 : {n : ℕ | ∃ a b : ℤ, n^2 = a + b ∧ n^3 = a^2 + b^2} = {0, 1, 2} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: if exists a, b, then n in {0, 1, 2}
    rintro ⟨a, b, h1, h2⟩
    have h3 : (n : ℤ) ^ 2 = a + b := by
      exact_mod_cast h1
    have h4 : (n : ℤ) ^ 3 = a ^ 2 + b ^ 2 := by 
      exact_mod_cast h2
    have h5 : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by 
      nlinarith [sq_nonneg (a - b)]
    have h6 : 2 * ((n : ℤ) ^ 3) ≥ ((n : ℤ) ^ 2) ^ 2 := by 
      have h7 : a + b = (n : ℤ) ^ 2 := by 
        linarith
      have h8 : a ^ 2 + b ^ 2 = (n : ℤ) ^ 3 := by 
        linarith
      nlinarith [sq_nonneg (a - b), h7, h8, h5]
    have h7 : (n : ℤ) ≤ 2 := by 
      nlinarith
    have h8 : n ≤ 2 := by 
      omega
    interval_cases n <;> omega 
  · -- Backward direction: if n in {0, 1, 2}, then exists a, b 
    rintro (h | h | h)
    · -- n = 0 
      rw [h]
      use 0, 0
      all_goals
        norm_num
    · -- n = 1 
      rw [h]
      use 0, 1
      all_goals 
        norm_num 
    · -- n = 2 
      rw [h]
      use 2, 2
      all_goals 
        norm_num