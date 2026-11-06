import Mathlib

open Set

theorem number_theory_5330 : {n : ℕ | (Nat.digits 5 n).length = 3}.ncard = 100 := by
  have : {n : ℕ | (Nat.digits 5 n).length = 3} = Set.Icc 25 124 := by
    ext n
    simp
    constructor
    · -- First, prove if (Nat.digits 5 n).length = 3, then 25 ≤ n ≤ 124
      intro h
      have h1 : n ≥ 25 := by 
        by_contra h1 
        push_neg at h1 
        interval_cases n <;> norm_num at h h1 
        <;> try { tauto }
      have h2 : n ≤ 124 := by
        by_contra h2 
        push_neg at h2 
        have h3 : (Nat.digits 5 n).length > 3 := by
          have h7 : (Nat.digits 5 n).length = Nat.log 5 (n) + 1 := by
            rw [Nat.digits_len]
            all_goals omega 
          rw [h7] at *
          have h8 : Nat.log 5 (n) ≥ 3 := by
            have h6 : n ≥ 125 := by 
              omega 
            have h7 : Nat.log 5 (n) ≥ 3 := by 
              apply Nat.le_log_of_pow_le (by norm_num) 
              all_goals omega 
            omega 
          omega 
        omega 
      constructor <;> try omega
    · -- Second, prove if 25 ≤ n ≤ 124, then (Nat.digits 5 n).length = 3
      rintro ⟨h1, h2⟩
      interval_cases n <;> norm_num
  rw [this]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }