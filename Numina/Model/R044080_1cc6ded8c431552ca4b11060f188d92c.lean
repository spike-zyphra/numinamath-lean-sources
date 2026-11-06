import Mathlib

theorem number_theory_247059 :
    {n : ℤ | (∃ m, m^2 = n + 100) ∧ (∃ p, p^2 = n + 164)} = {125, -64, -100} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨p, hp⟩⟩
    -- Now we have two equations:
    -- 1. `m^2 = n + 100`
    -- 2. `p^2 = n + 164`
    -- Subtracting the first from the second gives:
    -- `p^2 - m^2 = (n + 164) - (n + 100) = 64`
    have h1 : p^2 - m^2 = 64 := by
      nlinarith
    have h2 : (p - m) * (p + m) = 64 := by
      linarith [h1]
    have h3 : p - m ∣ 64 := by
      use p + m
      all_goals
        linarith [h2]
    have h4 : p - m ≤ 64 := by
      apply Int.le_of_dvd (by norm_num) h3
    -- Since $p - m \geq -64$.
    have h7 : p - m ≥ -64 := by
      have h8 : -(p - m) ∣ 64 := by
        exact Int.neg_dvd.2 h3
      have h9 : -(p - m) ≤ 64 := by
        apply Int.le_of_dvd (by norm_num) h8
      linarith
    interval_cases h10 : p - m <;> try { 
      omega
    } <;> try { 
      have h11 : p ≤ 32 := by nlinarith
      have h12 : p ≥ -32 := by nlinarith
      interval_cases p <;> omega
    } <;> try { 
      have h11 : m ≤ 32 := by nlinarith
      have h12 : m ≥ -32 := by nlinarith
      interval_cases m <;> omega
    }
  · rintro (rfl | rfl | rfl)
    · constructor
      · use 15
        all_goals norm_num
      · use 17
        all_goals norm_num
    · constructor
      · use 6
        all_goals norm_num
      · use 10
        all_goals norm_num
    · constructor
      · use 0
        all_goals norm_num
      · use 8
        all_goals norm_num