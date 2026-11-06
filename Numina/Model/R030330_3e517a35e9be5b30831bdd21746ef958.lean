import Mathlib

theorem algebra_21303 {n : ℕ} (hn : n = 125) :
    ∑' (i : ℕ), n / 5 ^ (i + 1)  = 31 := by
  rw [hn]
  have h125 : ∑' (i : ℕ), 125 / 5 ^ (i + 1) = 31 := by
    have h3 : ∀ (i : ℕ), i ≥ 4 → 125 / 5 ^ (i + 1) = 0 := by 
      intro i h
      have h4 : 5 ^ (i + 1) > 125 := by
        have h5 : i ≥ 4 := h
        have h6 : i + 1 ≥ 5 := by omega 
        have h7 : 5 ^ (i + 1) ≥ 5 ^ 5 := by
          apply Nat.pow_le_pow_of_le_right 
          all_goals omega 
        have h8 : 5 ^ 5 > 125 := by norm_num 
        linarith 
      have h10 : 125 / 5 ^ (i + 1) = 0 := by
        rw [Nat.div_eq_zero_iff] 
        omega 
      exact h10 
    have h7 : ∑' (i : ℕ), 125 / 5 ^ (i + 1) = ∑ i in Finset.range 4, 125 / 5 ^ (i + 1) := by 
      have h10 : ∀ (i : ℕ), i ∉ Finset.range 4 → 125 / 5 ^ (i + 1) = 0 := by
        intro i hi
        have h11 : i ≥ 4 := by
          simp [Finset.mem_range] at hi
          omega 
        apply h3 i 
        all_goals omega 
      rw [tsum_eq_sum] 
      intro i hi
      have h11 : i ≥ 4 := by
        simp [Finset.mem_range] at hi 
        omega 
      apply h3 i 
      all_goals omega 
    rw [h7] 
    norm_num [Finset.sum_range_succ] 
  exact h125