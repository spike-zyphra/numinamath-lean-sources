import Mathlib

theorem number_theory_7705 : {n : ℕ | 0 < n ∧ n ^ n ∣ 144 ^ 144}.encard = 20 := by
  have h1 : {n : ℕ | 0 < n ∧ n ^ n ∣ 144 ^ 144} = 
      Finset.filter (fun n => 0 < n ∧ n ^ n ∣ 144 ^ 144) (Finset.Icc 0 144) := by
    ext n
    simp
    intro h2 h3
    have h4 : n ≤ 144 := by
      by_contra h
      push_neg at h
      have h5 : n ^ n > 144 ^ 144 := by
        have h6 : n ≥ 145 := by linarith
        have h7 : n ^ n ≥ n ^ 145 := by
          have h8 : n ≥ 145 := by linarith
          have h9 : n ^ n ≥ n ^ 145 := by 
            apply Nat.pow_le_pow_of_le_right
            all_goals linarith
          linarith
        have h8 : n ^ 145 ≥ 145 ^ 145 := by
          have h9 : n ≥ 145 := by linarith
          have h10 : n ^ 145 ≥ 145 ^ 145 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals linarith
          linarith
        have h9 : 144 ^ 144 < 145 ^ 145 := by
          norm_num
        have h10 : 145 ^ 145 ≤ n ^ 145 := by linarith
        have h11 : 144 ^ 144 < n ^ 145 := by linarith
        have h12 : n ^ 145 ≤ n ^ n := by linarith
        linarith
      have h6 : n ^ n > 144 ^ 144 := h5
      have h7 : n ^ n ∣ 144 ^ 144 := h3
      -- contradiction
      have h8 : (144 ^ 144) % (n ^ n) = 0 := by
        exact Nat.mod_eq_zero_of_dvd h3
      have h9 : (144 ^ 144) < (n ^ n) := h5
      have h12 : (144 ^ 144) % (n ^ n) = (144 ^ 144) := by
        rw [Nat.mod_eq_of_lt]
        all_goals linarith
      linarith 
    tauto 
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide