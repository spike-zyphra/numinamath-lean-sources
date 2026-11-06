import Mathlib

theorem number_theory_320611 (n : ℕ) (h : n = 3^11) :
    IsGreatest {k | ∃ m, n = ∑ i ∈ Finset.range k, (m + i)} 486 := by
  rw [h] at *
  constructor
  · -- Show 486 is in the set 
    use 122
    native_decide
  · -- Show 486 is the greatest element in the set
    intro k hk
    rcases hk with ⟨m, hm⟩
    by_contra h1
    push_neg at h1
    have h0 : k > 486 := by 
      omega 
    have eq1 : ∑ i in Finset.range k, (m + i) = k * m + (k * (k - 1)) / 2 := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, Finset.card_range, Finset.sum_range_id, Nat.mul_comm k m]
      <;> ring_nf <;> omega
    have eq2 : k * m + (k * (k - 1)) / 2 = 3^11 := by 
      linarith [hm, eq1]
    have h3 : k ≤ 486 := by 
      by_contra h4
      push_neg at h4
      have h4' : k ≥ 487 := by
        omega
      have h5 : k ≤ 800 := by
        by_contra h6
        push_neg at h6
        have h7 : k * (k - 1) / 2 > 3^11 := by
          have h8 : k ≥ 801 := by
            omega
          have h9 : k - 1 ≥ 800 := by
            have : k ≥ 801 := h8
            omega
          have h10 : k * (k - 1) ≥ 801 * 800 := by
            nlinarith [h8, h9, show k ≥ 1 by omega]
          have h11 : k * (k - 1) / 2 ≥ (801 * 800) / 2 := by
            apply Nat.div_le_div
            all_goals 
              nlinarith
          have h12 : (801 * 800) / 2 = 320400 := by norm_num
          have h14 : k * (k - 1) / 2 ≥ 320400 := by 
            omega 
          have h13 : 3^11 = 177147 := by norm_num
          omega
        have h8 : k * m + (k * (k - 1)) / 2 = 3^11 := eq2
        have h9 : k * m ≥ 0 := by 
          nlinarith
        omega
      interval_cases k <;> omega
    omega
    all_goals 
      try { tauto }
      try { ring_nf }
      all_goals omega