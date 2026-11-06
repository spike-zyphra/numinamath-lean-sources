import Mathlib

theorem number_theory_138258 (m n : ℕ) (hm : m > 0) (hn : n > 0) :
    m^3 - n^3 = 999 ↔ (m = 10 ∧ n = 1) ∨ (m = 12 ∧ n = 9) := by
  constructor
  · -- First direction: from m^3 -n^3 =999 to the possible solutions
    intro h
    have h1 : m^3 = n^3 + 999 := by 
      omega
    -- We know m > n by positivity of m^3 -n^3
    have h2 : m > n := by
      by_contra h3
      push_neg at h3
      have h3' : m ≤ n := by linarith
      have h4 : m^3 ≤ n^3 := by
        apply Nat.pow_le_pow_of_le_left 
        all_goals linarith
      omega
    -- We bound n from above
    have h3 : n ≤ 18 := by
      by_contra h4
      push_neg at h4
      have h4' : n ≥ 19 := by linarith
      -- We know m ≥ n + 1
      have h5 : m ≥ n + 1 := by
        omega
      -- Therefore m^3 ≥ (n + 1) ^3
      have h6 : m^3 ≥ (n + 1) ^3 := by
        have h7 : m ≥ n + 1 := by linarith
        have h8 : m^3 ≥ (n + 1) ^3 := by
          apply Nat.pow_le_pow_of_le_left 
          all_goals linarith
        linarith
      -- But m^3 = n^3 + 999
      -- So n^3 + 999 ≥ (n + 1) ^3
      have h7 : n^3 + 999 ≥ (n + 1) ^3 := by
        nlinarith [h1, h6]
      -- This doesn't hold for n >= 19
      have h8 : n ≤ 18 := by
        nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((n : ℕ) - (19 : ℕ) : ℤ), sq_nonneg ((n : ℕ) + 1 : ℤ)]
      omega
    -- We bound m from above
    have h4 : m ≤ 19 := by
      have h5 : m^3 ≤ 6831 := by
        have h6 : m^3 = n^3 + 999 := h1
        have h7 : n^3 ≤ 5832 := by
          have h8 : n ≤ 18 := h3
          have h9 : n^3 ≤ 18^3 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals linarith
          norm_num at h9 ⊢
          linarith
        linarith [h6, h7]
      have h10 : m ≤ 19 := by
        by_contra h11
        push_neg at h11
        have h11' : m ≥ 20 := by omega
        have h12 : m^3 ≥ 8000 := by
          have h13 : m ≥ 20 := by omega
          have h14 : m^3 ≥ 20^3 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals linarith
          norm_num at h14 ⊢
          linarith
        linarith
      linarith
    interval_cases n <;> try { 
      interval_cases m <;> omega 
    } <;> try { tauto }
    <;> try { nlinarith }
    <;> try { nlinarith }
  · -- Second direction
    rintro (h | h)
    · -- First solution
      rcases h with ⟨rfl, rfl⟩
      all_goals
        norm_num
    · -- Second solution
      rcases h with ⟨rfl, rfl⟩
      all_goals
        norm_num