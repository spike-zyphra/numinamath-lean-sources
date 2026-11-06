import Mathlib

theorem number_theory_191462 :
    Set.ncard {x : ℕ | 0 < x ∧ (Nat.digits 10 (3 * x)).length = 3 ∧ (Nat.digits 10 (4 * x)).length = 4} = 84 := by
  have h1 : {x : ℕ | 0 < x ∧ (Nat.digits 10 (3 * x)).length = 3 ∧ (Nat.digits 10 (4 * x)).length = 4} = Set.Icc 250 333 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- First, prove the set's elements are in [250, 333]
      rintro ⟨hn_pos, h1, h2⟩
      have h3 : n ≥ 250 := by
        by_contra h
        push_neg at h
        interval_cases n <;> norm_num at h1 h2
      have h4 : n ≤ 333 := by
        by_contra h
        push_neg at h
        have h5 : n ≥ 334 := by omega
        have h6 : (Nat.digits 10 (3 * n)).length > 3 := by
          have h7 : 3 * n ≥ 1000 := by
            omega
          have h8 : (Nat.digits 10 (3 * n)).length > 3 := by
            have h9 : 3 * n ≥ 1000 := by
              omega
            have h10 : (Nat.log 10 (3 * n)) ≥ 3 := by 
              have : 10 ^ 3 ≤ 3 * n := by 
                omega
              have h12 : Nat.log 10 (3 * n) ≥ 3 := by 
                apply Nat.le_log_of_pow_le (by norm_num) this
              omega
            have h11 : (Nat.digits 10 (3 * n)).length = Nat.log 10 (3 * n) + 1 := by 
              rw [Nat.digits_len]
              all_goals linarith
            omega
          linarith
        simp_all
      constructor
      · -- Show n ≥ 250
        linarith
      · -- Show n ≤ 333
        linarith
    · -- Now prove the reverse: if $250 \leq n \leq 333$, then it's in the set
      rintro ⟨hn1, hn2⟩
      constructor
      · -- Show n > 0
        omega
      constructor
      · -- Show (Nat.digits 10 (3 * n)).length = 3
        interval_cases n <;> norm_num
      · -- Show (Nat.digits 10 (4 * n)).length = 4
        interval_cases n <;> norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp