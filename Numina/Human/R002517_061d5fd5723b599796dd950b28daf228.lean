import Mathlib

-- What is the largest 2-digit prime factor of the integer n = (200 choose 100)?

theorem AIME_number_theory_94495 : IsGreatest {p | p.Prime ∧ p ∣ Nat.choose 200 100 ∧ p < 100} 61 := by
  -- We need this statement in the Tactic state
  have : Fact (Nat.Prime 61) := by rw [fact_iff]; norm_num

  constructor

  -- First we prove that 61 is a prime factor of 200 choose 100
  · simp only [Set.mem_setOf_eq, Nat.reduceLT, and_true]
    constructor
    · norm_num
    · rw [dvd_iff_padicValNat_ne_zero (by rw [ne_eq, Nat.choose_eq_zero_iff]; linarith)]
      have log : Nat.log 61 200 < 2 := by rw [← Nat.lt_pow_iff_log_lt]; all_goals norm_num
      rw [padicValNat_choose (by norm_num) log]
      apply Finset.card_ne_zero_of_mem ?_
      use 1
      simp

    -- Now we prove that if p | 200 choose 100 and p < 100, then p ≤ 61
  · intro p hp
    -- We split the hypothesis
    obtain ⟨prime_p, div_p, bound_p⟩ := Set.mem_setOf_eq.mp hp
    -- Again we need this statement in the Tactic state
    have := fact_iff.mpr prime_p
    -- We need a bound on the exponent
    have log : Nat.log p 200 < 9 := by
      rw [← Nat.lt_pow_iff_log_lt] <;> norm_num
      · apply lt_of_lt_of_le (by norm_num : 200 < 2^9)
        exact Nat.pow_le_pow_of_le_left (Nat.Prime.two_le prime_p) 9
      · exact Nat.Prime.two_le prime_p

    -- We compute the exponent of p in 200 choose 100
    apply (one_le_padicValNat_of_dvd (by apply Nat.choose_pos; linarith )) at div_p
    rw [padicValNat_choose (by norm_num) log] at div_p

    -- x is such that p^x divides 200 choose 100
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp div_p
    simp only [Nat.reduceSub, Finset.filter_val, Multiset.mem_filter, Finset.mem_val,
      Finset.mem_Ico] at hx
    obtain ⟨⟨x_ge_1, x_lt_9⟩, hx⟩ := hx

    by_cases h : x < 2
    -- If x = 1, then p = 61
    · rw [(by linarith : x = 1), pow_one, Nat.mod_eq_sub_mod (Nat.le_of_succ_le bound_p),
        ← two_mul] at hx
      have := le_trans hx ((mul_le_mul_left (by norm_num : 0 < 2)).mpr (Nat.mod_le (100-p) p))
      rw [Nat.mul_sub, ← (add_le_add_iff_right (2*p)), Nat.sub_add_cancel (by linarith)] at this
      -- Now we can deduce that p < 67
      have : p < 67 := by linarith
      -- 61 is the largest prime less than 67
      interval_cases p <;> norm_num
      all_goals contradiction
    -- If x > 1, then all primes greater than 61 are such that p^x > 200
    · rw [← two_mul] at hx
      -- If p^2 <= 200, then p <= 14
      have := le_trans (pow_le_pow_right (NeZero.one_le) (Nat.le_of_not_lt h))
        (le_trans hx ((mul_le_mul_left (by norm_num : 0 < 2)).mpr (Nat.mod_le 100 (p^x))))
      have : p <= 14 := by apply Nat.le_sqrt'.mpr at this; norm_num at this; assumption
      linarith