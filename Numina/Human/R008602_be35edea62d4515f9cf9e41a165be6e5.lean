import Mathlib

/- Find the least positive integer $N$ such that the set of $1000$ consecutive integers beginning with $1000\cdot N$ contains no square of an integer. -/
theorem number_theory_95749 :
    IsLeast {N : ℕ | 0 < N ∧ ∀ k ∈ Finset.range 1000, ¬ ∃ m, m^2 = 1000 * N + k} 282 := by
  -- We need to prove that 282 works, and that no number less than 282 works.
  constructor
  -- First we prove that 282 works
  · simp only [Finset.mem_range, not_exists, Set.mem_setOf_eq, Nat.ofNat_pos, Nat.reduceMul, true_and]
    intro k hk x
    by_cases hx : x ≤ 531
    -- If x is less than 531, then its square is less than 282*1000
    · exact ne_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_of_le_left hx 2) (by linarith))
    -- If x is greater than 531, then its square is greater than 282*1000+1000
    · exact ne_of_gt (lt_of_lt_of_le (by linarith) (Nat.pow_le_pow_of_le_left (not_le.mp hx) 2))
  -- Now we prove that no number less than 282 works
  · simp only [lowerBounds, Finset.mem_range, not_exists, Set.mem_setOf_eq, and_imp]
    intro a apos hk
    contrapose! hk
    by_cases ha : a < 250
    -- If a is less than 250, then we can take the smallest square greater than 1000*a
    · use (Nat.sqrt (1000*a)+1)^2 - 1000*a
      constructor
      -- The difference between the square and 1000*a is less than 1000
      · have := Nat.lt_succ_sqrt' (1000 * a)
        rw [add_sq, mul_one, one_pow, tsub_lt_iff_left (by linarith), add_assoc]
        apply add_lt_add_of_le_of_lt (Nat.sqrt_le' (1000 * a))
        have : 2 * (1000 * a).sqrt < 999 := by
          apply (lt_of_pow_lt_pow_left' 2) (lt_of_lt_of_le _ (by linarith : 2^2*1000*a < 999^2))
          apply Nat.lt_succ_iff.mpr
          rw [mul_pow, mul_assoc]
          gcongr
          exact Nat.sqrt_le' (1000 * a)
        linarith
      -- And it is a square by definition
      · use Nat.sqrt (1000*a)+1
        rw [add_comm (1000*a), tsub_add_cancel_of_le]
        exact Nat.le_of_succ_le (Nat.lt_succ_sqrt' (1000 * a))
    -- If a is greater than 250, then we can write a = 250+c, and (500+c)^2 is in the range
    · obtain ⟨c, cpos, hc⟩ := le_iff_exists_nonneg_add.mp (not_lt.mp ha)
      use c^2
      rw [← hc, mul_add, (by norm_num : 1000 * 250 = 500^2)]
      constructor
      · exact lt_of_le_of_lt (Nat.pow_le_pow_of_le_left (by linarith : c ≤ 31) 2) (by linarith : 31^2 < 1000)
      · exact ⟨500+c, by linarith⟩