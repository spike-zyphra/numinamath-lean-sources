import Mathlib

open Real

theorem inequalities_95606 :
    Set.ncard {n : ℕ | 0 < n ∧ (130 * n) ^ 50 > n ^ 100 ∧ n ^ 100 > 2 ^ 200} = 125 := by
  have h1 : {n : ℕ | 0 < n ∧ (130 * n) ^ 50 > n ^ 100 ∧ n ^ 100 > 2 ^ 200} = Set.Icc 5 129 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume n in the set
      rintro ⟨h1, h2, h3⟩
      have h4 : n > 4 := by
        by_contra h
        push_neg at h
        have h5 : n ≤ 4 := by omega
        have h6 : n ^ 100 ≤ 4 ^ 100 := by
          have h7 : n ≤ 4 := h5
          have h8 : n ^ 100 ≤ 4 ^ 100 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals omega
          linarith
        have h7 : 4 ^ 100 = 2 ^ 200 := by
          norm_num
        have h8 : n ^ 100 ≤ 2 ^ 200 := by
          linarith [h6, h7]
        linarith
      have h5 : n < 130 := by
        by_contra h
        push_neg at h
        have h8 : n ≥ 130 := by omega
        have h9 : (130 * n) ^ 50 ≤ n ^ 100 := by
          have h7 : n ≥ 130 := h8
          have h9 : 130 ^ 50 ≤ n ^ 50 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals
              omega
          have h10 : (130 * n) ^ 50 = 130 ^ 50 * n ^ 50 := by
            ring_nf
          have h11 : 130 ^ 50 * n ^ 50 ≤ n ^ 50 * n ^ 50 := by
            have h12 : 130 ^ 50 ≤ n ^ 50 := h9
            nlinarith [h12, mul_pos (show (0 : ℕ) < 130 by norm_num) (show (0 : ℕ) < n by omega)]
          have h13 : n ^ 50 * n ^ 50 = n ^ 100 := by
            ring_nf
          linarith [h10, h11, h13]
        linarith
      have h5a : n ≤ 129 := by omega
      constructor
      · -- Show that n >= 5
        omega
      · -- Show that n <= 129
        omega
    · -- Show that if n in Set.Icc 5 129, then conditions hold
      rintro ⟨h1, h2⟩
      constructor
      · -- Show n > 0
        omega
      constructor
      · -- Show (130 * n) ^ 50 > n ^ 100
        have h3 : n ≤ 129 := by omega
        have h4 : n ≥ 5 := by omega
        interval_cases n <;> norm_num
      · -- Show n ^ 100 > 2 ^ 200
        have h4 : n ≥ 5 := by omega
        have h5 : n ^ 100 > 2 ^ 200 := by
          have h8 : n ^ 100 ≥ 5 ^ 100 := by
            have h9 : n ≥ 5 := h4
            have h10 : n ^ 100 ≥ 5 ^ 100 := by
              apply Nat.pow_le_pow_of_le_left
              all_goals
                omega
            linarith
          have h7 : 5 ^ 100 > 2 ^ 200 := by
            norm_num
          linarith [h8, h7]
        linarith
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }