import Mathlib

theorem my_favorite_theorem (SatisfyingA : Set ℕ) 
    (hA : SatisfyingA = 
      {A | ∃ b_initial_digits b_last_digit B,
        1 ≤ b_last_digit 
        ∧ b_last_digit ≤ 9
        ∧ 10^7 ≤ b_initial_digits 
        ∧ b_initial_digits < 10^8
        ∧ B = b_initial_digits * 10 + b_last_digit
        ∧ A = b_last_digit * 10^8 + b_initial_digits
        ∧ Nat.Coprime B 18 
        ∧ B > 222222222 
      }) :
    IsGreatest SatisfyingA 999999998 ∧
    IsLeast SatisfyingA 122222224 := by 
  simp only [hA]
  clear hA SatisfyingA
  constructor
  · -- Is greatest case
    -- We must show 999999998 is the greatest such number
    unfold IsGreatest
    constructor
    · -- Show that 999999998 belongs to the set.
      simp only [Nat.reducePow, gt_iff_lt, exists_and_left, exists_eq_left, Set.mem_setOf_eq]
      use 99999998, 9
      simp
      -- Compute the coprimeness
      norm_num
    · -- Show that any element in the set does not exceed 999999998
      simp [upperBounds]
      intro A b_initial_digits b_last_digit 
      intro h_b_last h_b_last' 
      intro h_b_init h_b_init'
      intro hA h_coprime18 h_lowerbound
      by_contra! h_lt_A
      have h_A_lt : A ≤ 999999999 := by linarith
      -- A is constrained to be 999999999, this is the only thing to rule out
      interval_cases A
      clear h_A_lt h_lt_A
      -- Froam this, the digits of B
      have hb' : b_initial_digits = 99999999 := by linarith
      have hb : b_last_digit = 9 := by linarith
      subst hb hb'
      -- Now inspect the hypothesis that this is coprime to 18
      contrapose! h_coprime18
      norm_num
  · -- Is least case
    -- We must show 122222224 is the least such number
    unfold IsLeast
    constructor
    · -- Show that 122222224 belongs to the set.
      simp
      use 22222224, 1
      simp
      norm_num
    · -- Show that no element in the set is less than 122222224
      simp [lowerBounds]
      intro A b_initial_digits b_last_digit 
      intro h_b_last h_b_last'
      intro h_b_init h_b_init'
      intro hA h_coprime18 h_lowerbound
      by_contra! h_lt_A
      have : A = 122222223 := by linarith
      subst this
      have hb' : b_initial_digits = 22222223 := by omega
      have hb : b_last_digit = 1 := by omega
      subst hb hb'
      contrapose! h_coprime18
      norm_num
