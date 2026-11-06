import Mathlib



theorem algebra_10335
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (han : ∀ n, a (n + 1) = ∑ i ∈ Finset.Icc 0 n, a i) :
    IsLeast {vn | ∃ n, a n > 5000 ∧ a n = vn} 8192 := by

  have ha1 : a 1 = 1 := by
    specialize han 0 
    norm_num [Finset.sum_Icc_succ_top, ha0] at han 
    linarith

  have ha2 : a 2 = 2 := by 
    specialize han 1 
    norm_num [Finset.sum_Icc_succ_top, ha0, ha1] at han 
    linarith

  have ha3 : a 3 = 4 := by 
    specialize han 2 
    norm_num [Finset.sum_Icc_succ_top, ha0, ha1, ha2] at han 
    linarith

  have h1 : ∀ (n : ℕ), a (n + 2) = 2 * a (n + 1) := by
    intro n
    have eq1 : a (n + 2) = ∑ i ∈ Finset.Icc 0 (n + 1), a i := by
      specialize han (n + 1)
      simpa using han
    have eq2 : ∑ i ∈ Finset.Icc 0 (n + 1), a i = (∑ i ∈ Finset.Icc 0 n, a i) + a (n + 1) := by
      rw [Finset.sum_Icc_succ_top]
      all_goals linarith 
    have eq3 : a (n + 1) = ∑ i ∈ Finset.Icc 0 n, a i := by 
      specialize han n 
      simpa using han 
    rw [eq1, eq2, eq3] 
    all_goals omega

  have h2 : ∀ (n : ℕ), a (n + 1) = 2 ^ n := by 
    intro n 
    induction n with 
    | zero => 
      simp [ha1] 
    | succ n ih => 
      calc 
        a ((n + 1) + 1) = a (n + 2) := by ring_nf 
        _ = 2 * a (n + 1) := by 
          specialize h1 n 
          simpa using h1 
        _ = 2 * (2 ^ n) := by 
          rw [ih] 
        _ = 2 ^ (n + 1) := by 
          ring_nf

  constructor 
  · -- First, show 8192 is attained.
    use 14 
    constructor
    · -- Show a 14 > 5000 
      have ha14 : a 14 = 8192 := by 
        have h214 : a 14 = 2 ^ 13 := by 
          specialize h2 13 
          simpa using h2 
        norm_num at h214 ⊢ 
        omega 
      omega 
    · -- Show a 14 = 8192 
      have ha14 : a 14 = 8192 := by 
        have h214 : a 14 = 2 ^ 13 := by 
          specialize h2 13 
          simpa using h2 
        norm_num at h214 ⊢ 
        omega 
      omega 
  · -- Show any `vn` in the set is ≥ 8192
    intro vn h
    rcases h with ⟨n, hn1, hn2⟩ 
    by_contra h'
    push_neg at h'
    have h4 : a n < 8192 := by 
      omega 
    have h3 : n ≤ 13 := by 
      by_contra h
      push_neg at h 
      have h5 : a n ≥ 8192 := by
        have h6 : n ≥ 14 := by 
          omega 
        have h414 : ∀ (k : ℕ), a (k + 14) ≥ 8192 := by
          intro k 
          have eq5 : a (k + 14) = 2 ^ (k + 13) := by
            calc 
              a (k + 14) = a ((k + 13) + 1) := by ring_nf 
              _ = 2 ^ (k + 13) := by 
                specialize h2 (k + 13)
                simpa using h2 
          have h7 : (2 ^ (k + 13) : ℕ) ≥ 8192 := by
            have h313 : k + 13 ≥ 13 := by 
              omega 
            have h52 : (2 : ℕ) ^ (k + 13) ≥ (2 : ℕ) ^ 13 := by 
              apply Nat.pow_le_pow_of_le_right 
              all_goals linarith 
            have h522 : (2 : ℕ) ^ 13 = 8192 := by norm_num 
            have h8 : (2 : ℕ) ^ (k + 13) ≥ 8192 := by 
              linarith 
            exact h8 
          linarith 
        specialize h414 (n - 14)
        have eq6 : (n - 14) + 14 = n := by 
          omega 
        rw [eq6] at h414 
        linarith 
      linarith 
    interval_cases n <;> norm_num [h2] at hn1 h4 hn2 <;> omega