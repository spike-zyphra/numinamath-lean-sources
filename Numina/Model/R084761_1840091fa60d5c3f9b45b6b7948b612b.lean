import Mathlib

theorem algebra_12593 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (n % 10 = 2 ∧ (n / 100) % 10 = 4) ∧ 9 ∣ n} = {432} := by 
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n in the set, we need to show n = 432
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, ⟨hn3, hn4⟩, hn5⟩
    interval_cases n <;> omega
  · -- Assume n = 432, we need to show it's in the set
    intro h
    rw [h]
    constructor
    · -- Show 432 in range [100,999]
      norm_num
    constructor
    · -- Show units digit is 2
      constructor
      · norm_num
      · -- Show hundreds digit is 4
        norm_num
    · -- Show 9 divides 432
      norm_num