import Mathlib

/- 14 Prove using elementary methods: There exist infinitely many triangular numbers that are also pentagonal numbers (i.e., numbers of the form $\frac{1}{2} k(3 k-1)$, where $k$ is a positive integer). -/
theorem number_theory_131061
  : {n : ℕ | (∃ x, 2 * n = x * (x + 1)) ∧ (∃ y, 2 * n = y * (3 * y - 1))}.Infinite
  := by
    -- we'll prove the set is infinite by finding an infinite sequence in it, that is eventually increasing
    refine Set.infinite_of_forall_exists_gt ?_

    -- let n be the lower bound on the nth element
    intro n
    -- simplify
    norm_num

    -- we'll generate the sequence by induction
    induction' n with n nh
    -- the base case is 1, which is both a triangular and pentagonal number
    · exists 1

      -- simplify
      norm_num
      -- then x = y = 1
      split_ands <;> exists 1
    -- let b be the previous value in the sequence,
    -- 2 * b = x * (x + 1)) and
    -- 2 * b = y * (3 * y - 1)
    · obtain ⟨b, ⟨⟨x, b1⟩, ⟨y, b2⟩⟩, lt⟩ := nh
      -- let the next x be x' = 7x + 12y + 1
      let x' := 7 * x + 12 * y + 1
      -- and the next y be y' = 4x + 7y + 1
      let y' := 4 * x + 7 * y + 1

      -- note that in 2 * (x' * (x' + 1) / 2) we can cancel the 2's
      have mul_div_eq : 2 * (x' * (x' + 1) / 2) = x' * (x' + 1) := by
        -- because the numerator is even
        rw [Nat.mul_div_eq_iff_dvd, ←even_iff_two_dvd]
        exact Nat.even_mul_succ_self x'

      -- the next b is (x' * (x' + 1)) / 2
      exists (x' * (x' + 1)) / 2
      split_ands
      -- the next x is x'
      · exists x'
      -- the next y is y'
      · exists y'
        -- simplify
        rw [mul_div_eq]

        -- we just need to show that y' * (3 * y' - 1) - x' * (x' + 1) is zero (considered as integers)
        suffices : y' * (3 * y' - 1) - x' * (x' + 1) = (0 : ℤ)
        · rw [sub_eq_zero] at this
          have y'_bound : 1 ≤ 3 * y' := by
            norm_num [y']
            omega
          norm_cast at this
          omega

        -- chain equalities
        calc (y' : ℤ) * (3 * (y' : ℤ) - 1) - (x' : ℤ) * ((x' : ℤ) + 1)
          -- expand x' and y'
          _ = (4 * x + 7 * y + 1) * (12 * x + 21 * y + 2) - (7 * x + 12 * y + 1) * (7 * x + 12 * y + 2) := by
            ring_nf
            push_cast
            ring_nf
          -- simplify to get expressions for 2 * b
          _ = y * (3 * y - 1) - x * (x + 1) := by ring
          -- which we know to be equal
          _ = 0 := by
            rw [sub_eq_zero]
            have y'_bound : 1 ≤ 3 * y := by
              have y_pos : y ≠ 0 := by
                by_contra eq
                norm_num [eq] at b2
                omega
              omega
            norm_cast
            omega
      -- we know that our choice of b, which is x' * (x' + 1) / 2, is larger than n + 1
      · unfold x'
        -- because it's at least as large as 2 * b
        have ltt : n + 1 < 2 * b := by omega

        -- chain
        refine lt_of_lt_of_le ltt ?_
        -- we have that 2 * b = x * (x + 1)
        · rw [b1]

          -- then we just have an expression with x, y and constants

          -- cancel division
          refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_

          -- simplify
          ring_nf

          -- move terms to RHS
          suffices : 0 ≤ 2 + x * 21 + x * y * 168 + x ^ 2 * 49 + y * 36 + y ^ 2 * 144 - x * 2 - x ^ 2 * 2
          · omega

          -- all natural numbers are non-negative
          omega