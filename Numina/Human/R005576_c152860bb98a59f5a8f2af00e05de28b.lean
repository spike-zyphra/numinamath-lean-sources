import Mathlib

/-Find the number of positive integers x less than 100 for which
(3: ℤ) ^ x + (5: ℤ) ^ x + (7: ℤ) ^ x + (11: ℤ) ^ x +(13: ℤ) ^ x + (17: ℤ) ^ x + (19: ℤ) ^ x)
is prime.-/

theorem number_theory_608939: {x: ℕ | (1 ≤ x) ∧ (Prime ((3: ℤ) ^ x + (5: ℤ) ^ x + (7: ℤ) ^ x + (11: ℤ) ^ x +(13: ℤ) ^ x + (17: ℤ) ^ x + (19: ℤ) ^ x))}.encard = 0 := by

  -- we show that the set is indeed empty --
  have set_eq: {x: ℕ | (1 ≤ x) ∧ (Prime ((3: ℤ) ^ x + (5: ℤ) ^ x + (7: ℤ) ^ x + (11: ℤ) ^ x +(13: ℤ) ^ x + (17: ℤ) ^ x + (19: ℤ) ^ x))} = ∅ := by
    simp [Set.eq_empty_iff_forall_not_mem]
    intro x
    intro b
    let a:= (3: ℤ) ^ x + (5: ℤ) ^ x + (7: ℤ) ^ x + (11: ℤ) ^ x +(13: ℤ) ^ x + (17: ℤ) ^ x + (19: ℤ) ^ x
    have ha: (3: ℤ) ^ x + (5: ℤ) ^ x + (7: ℤ) ^ x + (11: ℤ) ^ x +(13: ℤ) ^ x + (17: ℤ) ^ x + (19: ℤ) ^ x = a := by simp [a]
    by_contra a_prime
    rw [ha] at a_prime
    have ba: 4 ≤ a := by
      simp [a]
      have l1: 0 < 3 ^ x := by
        apply pow_pos
        norm_num
      have l2: 0 < 5 ^ x := by
        apply pow_pos
        norm_num
      have l3: 0 < 7 ^ x := by
        apply pow_pos
        norm_num
      have l4: 0 < 11 ^ x := by
        apply pow_pos
        norm_num
      have l5: 0 < 13 ^ x := by
        apply pow_pos
        norm_num
      have l6: 0 < 17 ^ x := by
        apply pow_pos
        norm_num
      have l7: 0 < 19 ^ x := by
        apply pow_pos
        norm_num
      linarith
    -- Now, we show the key step: a is divided by 3 --
    have dvd3: 3 ∣ a := by
      rw [← Int.modEq_zero_iff_dvd]
      simp [a]
      -- a id will be used later --
      have eq: 0 ^ x + (-1) ^ x + 1 ^ x + (-1) ^ x + 1 ^ x + (-1) ^ x + 1 ^ x = 3 * (1 ^ x + (-1) ^ x) := by
        ring_nf
        have eq1: 0 ^ x = 0 := by
          apply Nat.zero_pow_of_pos
          omega
        simp [eq1]
        omega
      have r: 3 ^ x + 5 ^ x + 7 ^ x + 11 ^ x + 13 ^ x + 17 ^ x + 19 ^ x ≡
        0 ^ x + (-1) ^ x + 1 ^ x + (-1) ^ x + 1 ^ x + (-1) ^ x + 1 ^ x [ZMOD 3] := by
        repeat apply Int.ModEq.add
        all_goals apply Int.ModEq.pow; decide

      calc
        3 ^ x + 5 ^ x + 7 ^ x + 11 ^ x + 13 ^ x + 17 ^ x + 19 ^ x ≡ 0 ^ x + (-1) ^ x + 1 ^ x + (-1) ^ x + 1 ^ x + (-1) ^ x + 1 ^ x [ZMOD 3] := by exact r
                                                                _ ≡ 3 * (1 ^ x + (-1) ^ x) [ZMOD 3] := by rw[eq]
                                                                _ ≡ 0 [ZMOD 3] := by rw [Int.modEq_zero_iff_dvd]; simp

    have eq3: a = 3 := by
      rw [← Int.natAbs_dvd_natAbs] at dvd3
      simp at dvd3
      rw [Nat.prime_dvd_prime_iff_eq] at dvd3
      zify at dvd3
      rw [show |a| = a by apply abs_of_nonneg; linarith] at dvd3
      rw [← dvd3]
      norm_num
      rw [← Int.prime_iff_natAbs_prime]
      exact a_prime
    rw [eq3] at ba
    tauto

-- Finally, count the cardinality of the set --
  simp [set_eq]