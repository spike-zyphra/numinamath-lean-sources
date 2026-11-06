import Mathlib

def is_interesting (n : ℕ) := (Nat.digits 10 n).sum = (Nat.digits 10 (3 * n + 11)).sum

/- A natural number $n$ is interesting if the sum of the digits of $n$ is equal to the sum of the digits of $3 n+11$. Verify that there are infinitely many interesting numbers.

# -/
theorem number_theory_255881 : {n | is_interesting n}.Infinite := by
    -- there's an infinite number of interesting numbers iff for every
    -- natural number k, there is an interesting number that is greater than k
    rw [Set.infinite_iff_exists_gt]


    intro k

    -- 9 * (10 ^ (k + 2)) + 8 is an interesting number
    exists 9 * (10 ^ (k + 2)) + 8

    -- we'll prove that it's interesting and that it's larger than k
    split_ands
    -- first that it's interesting
    · simp only [Set.mem_setOf_eq]
      unfold is_interesting

      -- LHS is equal to 17
      have lhs_eq : (Nat.digits 10 (9 * 10 ^ (k + 2) + 8)).sum = 17 := by
        trans (Nat.digits 10 (8 + 10 * (10 ^ (k + 1) * 9))).sum
        · ring_nf

        trans (8 :: Nat.digits 10 (10 ^ (k + 1) * 9)).sum
        · rw [Nat.digits_add] <;> omega

        trans (8 :: (List.replicate (k + 1) 0 ++ Nat.digits 10 9)).sum
        · rw [Nat.digits_base_pow_mul] <;> omega
        norm_num

      -- RHS is also equal to 17
      have rhs_eq : (Nat.digits 10 (3 * (9 * 10 ^ (k + 2) + 8) + 11)).sum = 17 := by
        trans (Nat.digits 10 (27 * 10 ^ (k + 2) + 35)).sum
        · ring_nf

        -- extract first digit
        rw [Nat.digits_of_two_le_of_pos, Nat.add_mod]

        -- larger digits can be discarded
        have pow_10_mod_10 : 27 * 10 ^ (k + 2) % 10 = 0 := by
          rw [Nat.mul_mod, Nat.pow_mod]
          norm_num

        -- 35 mod 10 is 5
        have threefive_mod_10 : 35 % 10 = 5 := by omega

        -- so the smallest digit is 5
        rw [pow_10_mod_10, threefive_mod_10]

        -- expand division of sum of natural numbers
        rw [Nat.add_div]

        -- 10 cancels in 27 * 10 ^ (k + 2) / 10
        have term_2 : 27 * 10 ^ (k + 2) / 10 = 27 * 10 ^ (k + 1) := by
          trans 27 * (10 ^ (k + 1) * 10) / 10
          · congr
          omega

        rw [term_2]

        -- for natural numbers, 35 / 10 is 3
        have threefive_div_10 : 35 / 10 = 3 := by omega

        -- simplify
        rw [threefive_div_10, threefive_mod_10, pow_10_mod_10]

        -- then we have a case match, but we know that one branch holds, as ¬10 ≤ 5
        have not_ite : ¬10 ≤ 0 + 5 := by omega
        simp only [not_ite, ↓reduceIte, add_zero]

        -- rewrite to make it clear that 3 is the smallest digit
        trans (5 :: Nat.digits 10 (3 + 10 * (10 ^ k * 27))).sum
        · congr 3
          omega

        -- extract 3
        trans (5 :: 3 :: Nat.digits 10 (10 ^ k * 27)).sum
        · rw [Nat.digits_add] <;> omega

        -- extract k zeros
        trans (5 :: 3 :: (List.replicate k 0 ++ Nat.digits 10 27)).sum
        · rw [Nat.digits_base_pow_mul] <;> omega

        -- then we see that the equality holds
        norm_num

        -- we used trivial bounds
        all_goals
        · omega

      -- so both sides are equal
      linarith

    -- now we'll prove that it's interesting
    · suffices : k < 10 ^ (k + 2)
      · omega
      -- take log
      refine Nat.lt_pow_of_log_lt (by omega) ?_
      -- log k is at most k
      have := Nat.log_le_self 10 k
      omega