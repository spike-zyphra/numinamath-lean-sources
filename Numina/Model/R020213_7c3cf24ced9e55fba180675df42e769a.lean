import Mathlib

theorem number_theory_149856 :
    IsLeast {n | ∃ a d : ℕ, a > 0 ∧ d > 0 ∧ n = ∑ i ∈ Finset.range 6, (a + d * i) ∧
      ∀ i ∈ Finset.range 6, Nat.Prime (a + d * i)} 492 := by 
  constructor
  · -- First, we prove 492 is indeed achievable.
    use 7, 30
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num [Finset.sum_range_succ]
    · intro i hi
      fin_cases hi <;> norm_num
  · -- Now, we prove 492 is minimal
    intro n hn
    rcases hn with ⟨a, d, ha, hd, hn, hprime⟩
    have h1 := hprime 0 (Finset.mem_range.mpr (by norm_num))
    have h2 := hprime 1 (Finset.mem_range.mpr (by norm_num))
    have h3 := hprime 2 (Finset.mem_range.mpr (by norm_num))
    have h4 := hprime 3 (Finset.mem_range.mpr (by norm_num))
    have h5 := hprime 4 (Finset.mem_range.mpr (by norm_num))
    have h6 := hprime 5 (Finset.mem_range.mpr (by norm_num))
    by_contra h
    push_neg at h
    rw [hn] at h 
    norm_num [Finset.sum_range_succ] at h
    have h4 : a ≤ 82 := by 
      omega
    have h5 : d ≤ 32 := by 
      omega
    interval_cases a <;> interval_cases d <;> norm_num [Nat.Prime] at h1 h2 h3 h4 h5 h6 <;> all_goals omega