import Mathlib

theorem number_theory_106251 : IsLeast {n | ∃ k, n = k ∧ 105 ∣ ∑ i ∈ Finset.range 100, (n + i)} 3 := by
  constructor
  · -- Show 3 is in the set
    use 3
    constructor
    · rfl
    · -- Show 105 divides the sum from i = 0 to 99 of (3 + i)
      native_decide
  · -- Show no number less than 3 is in the set
    intro n
    rintro ⟨k, rfl, hk⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { 
      norm_num [Finset.sum_range_succ] at hk 
    }