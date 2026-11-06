import Mathlib

theorem Number_Theory_609762: IsLeast {k: ℕ | (1 ≤ k) ∧ (∃ p q r s t: ℕ,  (p ^ 2 ∣ k) ∧ (q ^ 3 ∣ k) ∧ (r ^ 5 ∣ k) ∧ (s ^ 7 ∣ k) ∧ (t ^ 11 ∣ k)
∧ (p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ p ≠ t ∧ q ≠ r ∧ q ≠ s ∧ q ≠ t ∧ r ≠ s ∧ r ≠ t ∧ s ≠ t) ∧ (1 ≤ p) ∧ (1 ≤ q) ∧ (1 ≤ q) ∧(1 ≤ r) ∧(1 ≤ s) ∧ (1 ≤ t))} 1024 := by
  constructor
  · -- Show 1024 is in the set
    constructor
    · norm_num
    · -- Show existence of p, q, r, s, t
      use 16, 8, 4, 2, 1
      all_goals norm_num
  · -- Show no smaller element is in the set
    intro k ⟨hk1, ⟨p, q, r, s, t, h1, h2, h3, h4, h5, h_ne, hp1, hq1, hq2, hr1, hs1, ht1⟩⟩
    by_contra h
    push_neg at h
    have h6 : k < 1024 := h
    have h7 : p ≤ 32 := by
      by_contra h8
      push_neg at h8
      have h81 : p ^ 2 ≥ 1025 := by
        have : p ≥ 33 := by omega
        nlinarith
      have h82 : p ^ 2 ∣ k := h1
      have h83 : p ^ 2 ≤ k := by 
        exact Nat.le_of_dvd (by omega) h82
      linarith [h81, h83, h6]
    have h8 : q ≤ 10 := by
      by_contra h9
      push_neg at h9
      have h91 : q ^ 3 ≥ 1025 := by
        have : q ≥ 11 := by omega
        have h94 : q ^ 3 ≥ 1331 := by
          have h95 : q ≥ 11 := by omega
          have h96 : q ^ 3 ≥ 11 ^ 3 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals omega
          norm_num at h96 ⊢
          all_goals omega
        omega
      have h92 : q ^ 3 ∣ k := h2
      have h93 : q ^ 3 ≤ k := by 
        exact Nat.le_of_dvd (by omega) h92
      linarith [h91, h93, h6]
    have h9 : r ≤ 3 := by
      by_contra h10
      push_neg at h10
      have h11 : r ≥ 4 := by omega
      have h12 : r ^ 5 ∣ k := h3
      have h13 : r ^ 5 ≤ k := by
        exact Nat.le_of_dvd (by omega) h12
      have h14 : r ^ 5 ≥ 1024 := by
        have h15 : r ≥ 4 := by omega
        have h16 : r ^ 5 ≥ 4 ^ 5 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals omega
        norm_num at h16 ⊢
        all_goals omega
      have h15 : k ≥ 1024 := by
        linarith [h13, h14]
      linarith [h15, h6]
    have h10 : s ≤ 2 := by
      by_contra h11
      push_neg at h11
      have h111 : s ^ 7 ≥ 1025 := by
        have : s ≥ 3 := by omega
        have h94 : s ^ 7 ≥ 2187 := by
          have h95 : s ≥ 3 := by omega
          have h96 : s ^ 7 ≥ 3 ^ 7 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals omega
          norm_num at h96 ⊢
          all_goals omega
        omega
      have h112 : s ^ 7 ∣ k := h4
      have h113 : s ^ 7 ≤ k := by 
        exact Nat.le_of_dvd (by omega) h112
      linarith [h111, h113, h6]
    have h11 : t = 1 := by
      have ht11 : t ^ 11 ∣ k := h5
      have ht111 : t ≤ 1 := by
        by_contra h12
        push_neg at h12
        have ht14 : t ≥ 2 := by
          omega
        have ht15 : t ^ 11 ≥ 2048 := by
          have : t ≥ 2 := by omega
          have h95 : t ^ 11 ≥ 2 ^ 11 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals omega
          norm_num at h95 ⊢
          all_goals omega
        have ht151 : t ^ 11 ≤ k := by 
          exact Nat.le_of_dvd (by omega) ht11
        omega
      have : t = 1 := by
        interval_cases t <;> omega
      assumption
    have h17 : r ^ 5 ∣ k := h3
    have h18 : s ^ 7 ∣ k := h4
    interval_cases r <;> interval_cases s 
      <;> norm_num at h17 h18 h3 h4 
      <;> omega