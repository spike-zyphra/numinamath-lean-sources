import Mathlib

theorem number_theory_267160 :
    IsLeast {k : ℕ | 0 < k ∧ ∃ n : ℕ, (2^4 * 3^2 * 5^5 * k) = n^3} 60 := by
  constructor
  · -- Show 60 is indeed in the set and is positive
    constructor
    · norm_num
    · -- Show that there exists n such that 2^4 * 3^2 * 5^5 * 60 = n^3
      use 300
      all_goals norm_num
  · -- Show that 60 is the smallest
    intro k hk
    rcases hk with ⟨hk_pos, ⟨n, hn⟩⟩
    by_contra h
    push_neg at h
    have h1 : k < 60 := h
    have h2 : n^3 = 2^4 * 3^2 * 5^5 * k := by
      linarith [hn]
    have h3 : n ≤ 300 := by
      by_contra h
      push_neg at h
      have h4 : n^3 ≥ 301^3 := by
        have h5 : n ≥ 301 := by linarith
        have h6 : n^3 ≥ 301^3 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        linarith
      have h7 : (2^4 * 3^2 * 5^5 * k) ≥ 301^3 := by
        linarith [h4, hn]
      have h8 : k ≥ 60 := by
        by_contra h
        push_neg at h
        have h9 : k < 60 := by omega
        have h10 : (2^4 * 3^2 * 5^5 * k) < 301^3 := by
          interval_cases k <;> norm_num
          all_goals
            norm_num
        linarith [h10, h7]
      omega
    interval_cases n <;> try { 
      omega
    } <;> norm_num at h2 <;> omega