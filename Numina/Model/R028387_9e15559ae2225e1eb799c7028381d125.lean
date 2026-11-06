import Mathlib

theorem number_theory_277466 :
  {n : ℕ | (∃ k, n = k^2) ∧ n ∈ Finset.Icc 1000 9999 ∧ (n / 100) % 100 = (n % 100) + 1} =
  {8281} := by 
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n in the set, prove {8281}
    rintro ⟨⟨k, rfl⟩, ⟨hk1, hk2⟩, h⟩
    have h1 : k ≥ 32 := by
      nlinarith
    have h2 : k ≤ 99 := by
      nlinarith
    interval_cases k <;> norm_num at *
  · -- Assume {8281}, prove in the set
    intro h
    rw [h]
    constructor
    · -- There exists k s.t. 8281 = k^2
      use 91
      all_goals norm_num
    constructor
    · -- 8281 in the range
      norm_num
    · -- Check condition
      norm_num