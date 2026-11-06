import Mathlib

theorem number_theory_130299 (n : ℕ) (h₀ : n = 2) :
    {m | m ∈ Finset.Icc 1000 9999 ∧ (m / 100 + m % 100)^2 = m} =
    {2025, 3025, 9801} := by
  ext m
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First direction: if m is a 4-digit number number satisfying the condition, then m ∈ {2025, 3025, 9801}
    rintro ⟨⟨hm1, hm2⟩, hm⟩
    have h1 : m ≥ 1000 := by linarith
    have h2 : m ≤ 9999 := by linarith
    have h3 : (m / 100 + m % 100) ^ 2 = m := by
      nlinarith
    have h30 : m = 2025 ∨ m = 3025 ∨ m = 9801 := by
      have h6 : (m / 100 + m % 100) ≤ 99 := by
        nlinarith [sq_nonneg ((m / 100 + m % 100) : ℕ), sq_nonneg ((m : ℕ) - (m / 100 + m % 100) ^ 2 : ℤ)]
      interval_cases k : m / 100 + m % 100 <;> try { 
        omega
      } <;> try { 
        all_goals
        have h8 : m ≤ 9999 := by linarith
        interval_cases m <;> omega
      }
    tauto
  · -- Second direction: if m ∈ {2025, 3025, 9801}, then m is a 4-digit number number satisfying the condition
    rintro (rfl | rfl | rfl)
    · constructor
      · norm_num
      · all_goals norm_num
    · constructor
      · norm_num
      · all_goals norm_num
    · constructor
      · norm_num
      · all_goals norm_num