import Mathlib

theorem number_theory_15414 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k ∈ Finset.Icc 1 n, (n ^ 2 - n) % k ≠ 0} 5 := by 
  constructor
  · -- Show that 5 is indeed in the set, using k = 3.
    constructor
    · norm_num 
    · use 3 
      all_goals norm_num
  · -- We now prove that 5 is the least such integer.
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, hk_mem, hk_mod⟩⟩
    by_contra h 
    push_neg at h 
    have h1 : n < 5 := h 
    have h2 : k ∈ Finset.Icc 1 n := hk_mem 
    rw [Finset.mem_Icc] at h2 
    rcases h2 with ⟨hk1, hkn⟩
    have hn4 : n ≤ 4 := by omega 
    interval_cases n <;> interval_cases k <;> omega