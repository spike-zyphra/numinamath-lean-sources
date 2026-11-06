import Mathlib

theorem number_theory_122098 :
    {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (n / 1000) % 10 = (n / 100) % 10 ∧ (n / 10) % 10 = (n % 10) ∧ ∃ k, n = k^2} = {7744} := by 
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n is in the original set prove it's 7744
    rintro ⟨⟨hn1, hn2⟩, hn3, hn4, ⟨k, rfl⟩⟩
    have hk1 : k ≥ 32 := by nlinarith
    have hk2 : k ≤ 99 := by nlinarith
    interval_cases k <;> norm_num at *
  · -- Forward direction: if n is 7744 then it is in the original set
    intro hn
    rw [hn]
    constructor
    · exact ⟨by norm_num, by norm_num⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · use 88
      all_goals norm_num