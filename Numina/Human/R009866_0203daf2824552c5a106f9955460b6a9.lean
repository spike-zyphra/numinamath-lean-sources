import Mathlib

/-Determine all pairs of strictly positive integers (m, n) such that
mn - 1 ∣ n ^ 3 - 1-/
theorem number_theory_607381: {(m, n): ℤ × ℤ | 0 < m ∧ 0 < n ∧ m * n - 1∣ n ^ 3 - 1}
 = {(m, n): ℤ × ℤ | 0 < m ∧ 0 < n ∧ (m = 1 ∨ n = 1 ∨ m = n ^ 2 ∨ n = m ^ 2)} := by
  ext ⟨m,n⟩
  constructor
  -- the forward direction
  . intro h
    simp only [Set.mem_setOf_eq] at h
    simp [h]
    rcases h with ⟨hm, hn, h⟩
    by_contra! no -- for convenience, we use the contradiction
    replace hm: 2 ≤ m := by omega
    replace hn: 2 ≤ n := by omega
    rcases no with ⟨no1,no2,p,q⟩
    clear no1 no2
    have d1: m * n - 1 ∣ (m * n) ^ 3 - 1 := by
      rw [show (m * n) ^ 3 - 1 = (m * n - 1) * ((m * n) ^ 2 + m * n + 1) by ring]
      simp
    have h': m * n - 1 ∣m ^ 3 - 1 := by  -- we show the symmetry
       rw [show m ^ 3 - 1 = ((m * n) ^ 3 - 1) - m ^ 3 * (n ^ 3 - 1) by ring]
       apply Int.dvd_sub
       exact d1
       have o: n ^ 3 - 1 ∣ m ^ 3 * (n ^ 3 - 1) := by simp
       apply dvd_trans h o
    have ineq1: m ≤ n ^ 2 := by  --show the first inequality
       apply exists_eq_mul_right_of_dvd at h
       obtain ⟨k, hk⟩ := h
       have l1: 0 ≤ n ^ 3 - 1 := by
        simp
        ring_nf
        have o2: 1 ≤ n ^ 3 := by
          rw [show (1: ℤ) = 1 ^ 3 by norm_num]
          rw [pow_le_pow_iff_left₀]
          all_goals omega
        nlinarith
       have l2: 0 ≤ m * n - 1 := by nlinarith
       have o: 0 ≤ k := by nlinarith
       have ne: k ≠ 0 := by
        by_contra! l
        simp [l] at hk
        have contra: 0 < n ^ 3 - 1 := by
          simp
          ring_nf
          have j: 2 ^ 3 ≤ n ^ 3 := by
            rw [pow_le_pow_iff_left₀]
            all_goals omega
          calc
            (1: ℤ) < 8 := by norm_num
             _= 2 ^ 3 := by norm_num
             _≤ n ^ 3 := by nlinarith
        rw [hk] at contra
        tauto
       have lk: 1 ≤ k := by omega
       have l: (m * n - 1) ≤ n ^ 3 - 1 := by
         rw [hk]
         nlinarith
       replace l: m * n ≤ n ^ 3 := by nlinarith
       nlinarith
    have ineq1': n ≤ m ^ 2 := by  --show the second inequality by symmetry
       apply exists_eq_mul_right_of_dvd at h'
       obtain ⟨k, hk⟩ := h'
       have l1: 0 ≤ m ^ 3 - 1 := by
        simp
        ring_nf
        have o2: 1 ≤ m ^ 3 := by
          rw [show (1: ℤ) = 1 ^ 3 by norm_num]
          rw [pow_le_pow_iff_left₀]
          all_goals omega
        nlinarith
       have l2: 0 ≤ m * n - 1 := by nlinarith
       have o: 0 ≤ k := by nlinarith
       have ne: k ≠ 0 := by
        by_contra! l
        simp [l] at hk
        have contra: 0 < m ^ 3 - 1 := by
          simp
          ring_nf
          have j: 2 ^ 3 ≤ m ^ 3 := by
            rw [pow_le_pow_iff_left₀]
            all_goals omega
          calc
            (1: ℤ) < 8 := by norm_num
             _= 2 ^ 3 := by norm_num
             _≤ m ^ 3 := by nlinarith
        rw [hk] at contra
        tauto
       have lk: 1 ≤ k := by omega
       have l: (m * n - 1) ≤ m ^ 3 - 1 := by
         rw [hk]
         nlinarith
       replace l: m * n ≤ m ^ 3 := by nlinarith
       nlinarith
    by_cases lmn: n ≤ m
    -- the case n ≤ m
    . have d2: m * n - 1 ∣ n * (n ^ 2 - m) := by  -- show the divisibility to give a inequality
        rw [show n * (n ^ 2 - m) = n ^ 3 - 1 - (m * n - 1) by ring_nf]
        apply Int.dvd_sub
        exact h
        rfl
      replace d2: m * n - 1 ∣ n ^ 2 - m := by  -- note that left is coprime with n
        have H1: IsCoprime (m * n - 1) n := by
          have o: IsCoprime ((m * n - 1) + (-m) * n) n := by
            rw [show (m * n - 1) + (-m) * n = -1 by ring]
            rw [show n = -(-n) by ring]
            rw [IsCoprime.neg_neg_iff]
            apply isCoprime_one_left
          rw [IsCoprime.add_mul_right_left_iff] at o
          exact o
        apply IsCoprime.dvd_of_dvd_mul_left H1 d2
      apply exists_eq_mul_right_of_dvd at d2
      obtain ⟨k, hk⟩ := d2
      have o: n ^ 2 - m < m * n - 1 := by
        nlinarith
      rw [hk] at o
      have i: k = 0 := by nlinarith
      simp [i] at hk
      replace hk: m = n ^ 2 := by omega
      tauto
    -- the case n > m, it's similar
    . have d2: m * n - 1 ∣ m * (m ^ 2 - n) := by  -- show the divisibility to give a inequality
        rw [show m * (m ^ 2 - n) = m ^ 3 - 1 - (m * n - 1) by ring_nf]
        apply Int.dvd_sub
        exact h'
        rfl
      replace d2: m * n - 1 ∣ m ^ 2 - n := by  -- note that left is coprime with m
        have H1: IsCoprime (m * n - 1) m := by
          have o: IsCoprime ((m * n - 1) + (-n) * m) m := by
            rw [show (m * n - 1) + (-n) * m = -1 by ring]
            rw [show m = -(-m) by ring]
            rw [IsCoprime.neg_neg_iff]
            apply isCoprime_one_left
          rw [IsCoprime.add_mul_right_left_iff] at o
          exact o
        apply IsCoprime.dvd_of_dvd_mul_left H1 d2
      apply exists_eq_mul_right_of_dvd at d2
      obtain ⟨k, hk⟩ := d2
      have o: m ^ 2 - n < m * n - 1 := by
        nlinarith
      rw [hk] at o
      have i: k = 0 := by nlinarith
      simp [i] at hk
      replace hk: n = m ^ 2 := by omega
      tauto

  -- the backward direction
  . intro h
    simp only [Set.mem_setOf_eq] at h
    simp [h]
    rcases h with ⟨hm, hn, h⟩
    rcases h with h | h | h | h
    all_goals simp [h]
    -- the case m = 1
    . rw [show n ^ 3 - 1 = (n - 1) * (n ^ 2 + n + 1) by ring]
      simp
    -- the cases n = 1
    . ring_nf
      rfl
    -- the case m = n ^ 2
    . rw [show m * m ^ 2 = m ^ 3 by ring]
      rw [show (m ^ 2) ^ 3 = m ^ 6 by ring]
      rw [show m ^ 6 - 1 = (m ^ 3 - 1) * (m ^ 3 + 1) by ring]
      simp