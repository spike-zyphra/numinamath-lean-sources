import Mathlib

theorem number_theory_270994 :
    IsLeast {m : ℕ | 0 < m ∧ ∑ i ∈ Finset.range 10, (m % (i + 1)) = 4} 120 := by
  constructor
  · -- Show that 120 is in the set
    constructor
    · norm_num
    · -- Calculate the sum of remainders for 120
      native_decide
  · -- Show that 120 is the smallest element in the set
    intro m hm
    rcases hm with ⟨hm_pos, hm_sum⟩
    by_contra h 
    push_neg at h
    -- Now m < 120
    interval_cases m <;> norm_num [Finset.sum_range_succ] at hm_sum <;> all_goals omega