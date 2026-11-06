import Mathlib

theorem number_theory_229846 :
    IsLeast {n : ℕ | n > 0 ∧ n % 10 = 2 ∧ 
    2 * n = (n % 10) * 10^(Nat.digits 10 (n / 10)).length + (n / 10)} 105263157894736842 := by 
  constructor 
  · -- Show 105263157894736842 is in the set 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    · native_decide 
  · -- Show it's minimal 
    intro n hn 
    rcases hn with ⟨hn1, hn2, hn3⟩ 
    by_contra h 
    push_neg at h 
    have h1 : n < 105263157894736842 := h 
    have h4 : n % 10 = 2 := hn2 
    have h5 : n / 10 < 10526315789473684 := by 
      omega 
    by_cases h8 : n / 10 = 0 
    · -- Case where n / 10 = 0 
      have h9 : n < 10 := by 
        omega 
      interval_cases n <;> norm_num at hn1 hn2 hn3 
    · -- Case where n / 10 > 0 
      have hne : n / 10 > 0 := by 
        omega 
      have h6 : (n / 10) < 10 ^ 17 := by 
        norm_num 
        all_goals 
          omega 
      have h7 : (Nat.digits 10 (n / 10)).length ≤ 17 := by 
        have h10 : (n / 10) < 10 ^ 17 := h6 
        have h11 : (Nat.digits 10 (n / 10)).length ≤ 17 := by 
          have h12 : (n / 10) < (10 : ℕ)  ^ 17 := h10 
          have h60 : (Nat.digits 10 (n / 10)).length ≤ 17 := by 
            have h40 : (n / 10) < (10 : ℕ)  ^ 17 := h12 
            have h41 : (Nat.log 10 (n / 10)) < 17 := by 
              apply Nat.log_lt_of_lt_pow 
              all_goals 
                omega 
            have h42 : (Nat.digits 10 (n / 10)).length = Nat.log 10 (n / 10) + 1 := by 
              rw [Nat.digits_len] 
              all_goals 
                omega 
            omega 
          assumption 
        assumption 
      interval_cases k : (Nat.digits 10 (n / 10)).length <;> norm_num [h4] at hn3 
      <;> omega