import Mathlib

theorem number_theory_52569 : {n : ℕ| 133^5 + 110^5 + 84^5 + 27^5 = n^5} = {144} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Let's prove the forward direction: if 133^5 + 110^5 + 84^5 + 27^5 = n^5, then n = 144
    intro h
    have h1 : n^5 = 133^5 + 110^5 + 84^5 + 27^5 := by
      linarith
    have h2 : n ≤ 144 := by
      by_contra h
      push_neg at h
      have h3 : n ≥ 145 := by 
        omega
      have h4 : n^5 ≥ 145^5 := by
        have h5 : n ≥ 145 := h3
        have h6 : n^5 ≥ 145^5 := by 
          apply Nat.pow_le_pow_of_le_left h5 5
        linarith
      nlinarith [h1, h4]
    have h4 : n ≥ 144 := by 
      by_contra h
      push_neg at h
      have h5 : n ≤ 143 := by 
        omega
      have h6 : n^5 ≤ 143^5 := by 
        have h7 : n ≤ 143 := h5
        have h8 : n^5 ≤ 143^5 := by 
          apply Nat.pow_le_pow_of_le_left h7 5
        linarith
      nlinarith [h1, h6]
    linarith [h2, h4]
  · -- Now the reverse direction: if n = 144, then 133^5 + 110^5 + 84^5 + 27^5 = n^5
    intro h
    rw [h]
    all_goals
      norm_num