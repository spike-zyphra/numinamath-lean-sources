import Mathlib

theorem number_theory_4654 {A : ℕ} (hA : A > 0) (hA1 : A ^ 8 = 78310985281) :
    A = 23 := by 
  have h1 : A ^ 8 = 23 ^ 8 := by
    norm_num [hA1]
  have h2 : A = 23 := by
    have h3 : A ^ 8 = 23 ^ 8 := h1
    have h4 : A = 23 := by
      have hA8 : A ^ 8 = 23 ^ 8 := h3
      have h5 : A <= 23 ∨ 23 <= A := by
        by_cases h : A <= 23
        · left
          exact h
        · right
          linarith
      rcases h5 with h5 | h5
      · -- Case 1: A <= 23
        interval_cases A <;> norm_num at hA8 <;> all_goals omega
      · -- Case 2: 23 <= A
        have h6 : A >= 23 := by linarith
        by_cases h7 : A < 24
        · -- 23 <= A < 24, so A = 23
          interval_cases A <;> norm_num at hA8 <;> all_goals omega
        · -- A >= 24
          have h7 : A >= 24 := by linarith
          have h8 : A ^ 8 >= 24 ^ 8 := by
            apply Nat.pow_le_pow_of_le_left
            linarith
          have h9 : 24 ^ 8 > 23 ^ 8 := by
            norm_num
          have h10 : A ^ 8 > 23 ^ 8 := by linarith
          linarith
    exact h4
  exact h2