import Mathlib

theorem number_theory_285572 : IsGreatest {n | n ^ 6021 < 2007 ^ 2007} 12 := by
  constructor
  · -- Show 12 is in the set
    show (12 : ℕ) ^ 6021 < 2007 ^ 2007
    norm_num
  · -- Show no larger element is in the set
    intro n hn
    have h : n ^ 6021 < 2007 ^ 2007 := by
      simpa using hn
    by_contra h'
    push_neg at h'
    have h2 : n ≥ 13 := by linarith
    have h4 : n ≥ 13 := by linarith
    have h5 : n ^ 3 ≥ 13 ^ 3 := by
      apply Nat.pow_le_pow_of_le_left
      linarith
      all_goals nlinarith
    have h6 : n ^ 6021 = (n ^ 3) ^ 2007 := by
      ring_nf
    have h88888 : (n ^ 3) ^ 2007 ≥ (2197 : ℕ) ^ 2007 := by
      have h44 : n ^ 3 ≥ (2197 : ℕ) := by
        have h2 : n >= 13 := by linarith
        have h55 : n ^ 3 >= 13 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
          all_goals linarith
        norm_num at h55 ⊢
        all_goals linarith
      have h88 : (n ^ 3) ^ 2007 >= (2197 : ℕ) ^ 2007 := by
        apply Nat.pow_le_pow_of_le_left
        exact h44
        all_goals omega
      exact h88
    have h8888888888 : (2197 : ℕ) ^ 2007 ≥ (2007 : ℕ) ^ 2007 := by
      norm_num
      all_goals try { tauto }
      all_goals try { norm_num }
      all_goals tauto
    have h3 : n ^ 6021 ≥ 2007 ^ 2007 := by
      rw [h6]
      have h9 : (n ^ 3) ^ 2007 ≥ (2007 : ℕ) ^ 2007 := by
        have h99 : (n ^ 3) ^ 2007 >= (2197 : ℕ) ^ 2007 := h88888
        have h999 : (2197 : ℕ) ^ 2007 >= (2007 : ℕ) ^ 2007 := h8888888888
        linarith
      linarith
    linarith
    all_goals try { tauto }
    all_goals try { norm_num }
    all_goals tauto