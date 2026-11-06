import Mathlib
/- How many positive integers $x$ are there such that $3 x$ has 3 digits and $4 x$ has four digits? -/
theorem number_theory_611453 : {x : ℕ | x > 0 ∧ (Nat.digits 10 (3 * x)).length = 3 ∧ (Nat.digits 10 (4 * x)).length = 4}.ncard = 84:= by
  -- We first prove that the set of valid x values is exactly the integers from 250 to 333 inclusive
  have h1 : {x : ℕ | x > 0 ∧ (Nat.digits 10 (3 * x)).length = 3 ∧ (Nat.digits 10 (4 * x)).length = 4} = Set.Icc 250 333:= by
    ext x
    constructor
    .
      -- Forward direction: if x satisfies our conditions, then 250 ≤ x ≤ 333
      intro h
      simp at h
      rcases h with ⟨h, h1, h2⟩
      rw [Nat.digits_len _ _ (by omega) (by omega)] at h1
      rw [Nat.digits_len _ _ (by omega) (by omega)] at h2
      replace h1 : Nat.log 10 (3 * x) = 2:= by omega
      replace h2 : Nat.log 10 (4 * x) = 3:= by omega
      replace h1 : Nat.log 10 (3 * x) < 3:= by omega
      replace h2 : Nat.log 10 (4 * x) ≥ 3:= by omega
      replace h1 : 3 * x < 10 ^ 3:= by exact Nat.lt_pow_of_log_lt (by omega) h1
      replace h2 : 4 * x ≥ 10 ^ 3:= by exact Nat.pow_le_of_le_log (by omega) h2
      simp at h1 h2
      replace h1 : x ≤ 333:= by omega
      simp
      constructor
      all_goals
        omega
    .
      -- Reverse direction: if 250 ≤ x ≤ 333, then x satisfies our conditions
      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      simp
      refine ⟨(by omega), ?_, ?_⟩
      .
        -- Proving that 3x has exactly 3 digits
        rw [Nat.digits_len _ _ (by omega) (by omega)]
        have h3 : Nat.log 10 (3 * x) < 3:= by exact Nat.log_lt_of_lt_pow (by omega) (by linarith)
        have h4 : Nat.log 10 (3 * x) ≥ 2:= by exact Nat.le_log_of_pow_le (by omega) (by linarith)
        linarith
      .
        -- Proving that 4x has exactly 4 digits
        rw [Nat.digits_len _ _ (by omega) (by omega)]
        have h3 : Nat.log 10 (4 * x) < 4:= by exact Nat.log_lt_of_lt_pow (by omega) (by linarith)
        have h4 : Nat.log 10 (4 * x) ≥ 3:= by exact Nat.le_log_of_pow_le (by omega) (by linarith)
        linarith

  -- Now we use the characterization to count the elements in the set
  rw [h1]
  clear h1
  -- Convert from Set to Finset for counting
  rw [show Set.Icc 250 333 = Finset.Icc 250 333 by simp]
  rw [Set.ncard_coe_Finset]
  -- Calculate the cardinality of the interval [250, 333]
  rw [Nat.card_Icc 250 333]
