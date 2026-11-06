import Mathlib

/- Find the largest positive integer $n$ such that $n^3+4n^2-15n-18$ is the
cube of an integer -/
theorem algebra_608407 :
    IsGreatest { n : ℤ | n > 0 ∧ ∃ t : ℤ, t ^ 3 = n ^ 3 + 4 * n ^ 2 - 15 * n - 18 } 19 := by

    constructor
    · simp
      use 20
      norm_num
    · -- then we show that 19 is the largest one
      unfold upperBounds
      simp_all

      -- consider any solution n, such that n > 0 and
      -- n ^ 3 + 4 * n ^ 2 - 15 * n - 18 = t ^ 3 for some t
      intro n n_pos t t_cube

      rcases lt_or_ge n 4 with n_lt_4 | n_ge_4
      · -- we do not need to consider the case n < 4, as this is trivial
        linarith
      · -- in case n ≥ 4, we aim to show that any solution is no bigger than 19

        -- first we show that n - 2 < t < n + 2
        have t_lt : t < n + 2 := by
          by_contra! ht
          -- if otherwise, t ≥ n + 2, then t ^ 3 ≥ n ^ 3 + 6 * n ^ 2 + 12 * n + 8
          have : t ^ 3 ≥ (n + 2) ^ 3 := by refine pow_le_pow_left₀ ?ha ht 3; linarith
          rw [t_cube] at this
          -- but n ^ 3 + 6 * n ^ 2 + 12 * n + 8 > n ^ 3 + 4 * n ^ 2 - 15 * n - 18
          nlinarith
        have t_gt : t > n - 2 := by
          by_contra! ht
          -- if otherwise, t ≤ n + 2, then t ^ 3 ≤ n ^ 3 - 6 * n ^ 2 + 12 * n - 8
          have : t ^ 3 ≤ (n - 2) ^ 3 := by
            apply pow_le_pow_left₀ ?_ ht 3
            have : n ^ 3 + 4 * n ^ 2 - 15 * n - 18 > 0 := by nlinarith
            by_contra! ht
            have : t ^ 3 < 0 := by refine Odd.pow_neg ?hn ht; exact Nat.odd_iff.mpr rfl
            linarith
          rw [t_cube] at this
          -- but n ^ 3 + 6 * n ^ 2 + 12 * n + 8 < n ^ 3 + 4 * n ^ 2 - 15 * n - 18
          -- when n ≥ 4
          nlinarith

        -- therefore, we must have t ∈ {n - 1, n, n + 1}
        have : t = n - 1 ∨ t = n ∨ t = n + 1 := by
          by_contra! h
          obtain ⟨ha, ⟨hb, hc⟩⟩ := h
          have : t ≤ n + 1 := by apply Int.le_of_lt_add_one; linarith
          have : t ≥ n - 1 := by apply Int.le_of_lt_add_one; linarith
          have : t < n + 1 := by apply lt_of_le_of_ne; linarith; assumption
          have : t > n - 1 := by apply lt_of_le_of_ne; linarith; exact ha.symm
          have : t = n := by linarith
          contradiction

        -- we divide into these 3 cases
        rcases this with h1 | h2 | h3
        · -- case 1: t = n - 1
          -- we have (n - 1) ^ 3 = n ^ 3 + 4 * n ^ 2 - 15 * n - 18
          rw [h1] at t_cube
          -- expand (n - 1) ^ 3, we deduce
          -- n ^ 3 - 3 * n ^ 2 + 3 * n - 1 = n ^ 3 + 4 * n ^ 2 - 15 * n - 18
          rw [show (n - 1) ^ 3 = n ^ 3 - 3 * n ^ 2 + 3 * n - 1 by ring] at t_cube
          -- reform the equation, we get 7 * n ^ 2 - 18 * n - 17 = 0
          have : 7 * n ^ 2 - 18 * n - 17 = 0 := by linarith
          -- In the original solution, it was showed that the above equation admits 
          -- no integral solution, deriving a contradiction.
          -- Here instead we directly conduct a number-theoretical analysis to simplify the proof

          -- by modulo n at both sides, we show that n is a divisor of 17
          have ha : 7 * n ^ 2 - 18 * n - 17 ≡ 0 [ZMOD n] := congrFun (congrArg HMod.hMod this) n
          have hb : 7 * n ^ 2 - 18 * n ≡ 17 [ZMOD n] := Int.ModEq.add_right_cancel' (-17) ha
          have hc : 7 * n ^ 2 - 18 * n ≡ 0 [ZMOD n] := by
            apply Dvd.dvd.modEq_zero_int
            apply Int.dvd_sub
            · rw [pow_two, ← mul_assoc]
              exact Int.dvd_mul_left (7 * n) n
            · exact Int.dvd_mul_left 18 n
          have : 17 ≡ 0 [ZMOD n] := by trans (7 * n ^ 2 - 18 * n); exact hb.symm; exact hc
          have n_dvd_17 : n ∣ 17 := by exact Int.dvd_of_emod_eq_zero this
          -- but then we must have n ≤ 17 ≤ 19, finishing the proof
          have : n ≤ 17 := by apply Int.le_of_dvd (show 17 > 0 by norm_num) n_dvd_17
          linarith
        · -- case 2: t = n
          -- we have n ^ 3 = n ^ 3 + 4 * n ^ 2 - 15 * n - 18
          rw [h2] at t_cube
          -- reform the equation, we get 7 * n ^ 2 - 18 * n - 17 = 0
          have : 4 * n ^ 2 - 15 * n - 18 = 0 := by linarith
          -- Here we conduct again a number-theoretical analysis.
          -- by modulo n at both sides, we show that n is a divisor of 18
          have ha : 4 * n ^ 2 - 15 * n - 18 ≡ 0 [ZMOD n] := congrFun (congrArg HMod.hMod this) n
          have hb : 4 * n ^ 2 - 15 * n ≡ 18 [ZMOD n] := Int.ModEq.add_right_cancel' (-18) ha
          have hc : 4 * n ^ 2 - 15 * n ≡ 0 [ZMOD n] := by
            apply Dvd.dvd.modEq_zero_int
            apply Int.dvd_sub
            · rw [pow_two, ← mul_assoc]
              exact Int.dvd_mul_left (4 * n) n
            · exact Int.dvd_mul_left 15 n
          have : 18 ≡ 0 [ZMOD n] := by trans (4 * n ^ 2 - 15 * n); exact hb.symm; exact hc
          have n_dvd_18 : n ∣ 18 := by exact Int.dvd_of_emod_eq_zero this
          -- but then we must have n ≤ 18 ≤ 19, finishing the proof
          have : n ≤ 18 := by apply Int.le_of_dvd (show 18 > 0 by norm_num) n_dvd_18
          linarith
        · -- case 3: t = n + 1
          -- we have (n + 1) ^ 3 = n ^ 3 + 4 * n ^ 2 - 15 * n - 18
          rw [h3] at t_cube
          -- expand (n + 1) ^ 3, we deduce
          -- n ^ 3 + 3 * n ^ 2 + 3 * n + 1 = n ^ 3 + 4 * n ^ 2 - 15 * n - 18
          rw [show (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 by ring] at t_cube
          -- reform the equation, we get n ^ 2 - 18 * n - 19 = 0
          have eq : n ^ 2 - 18 * n - 19 = 0 := by linarith
          -- factorize LHS
          have : n ^ 2 - 18 * n - 19 = (n + 1) * (n - 19) := by ring
          rw [this] at eq
          -- we deduce n = -1 or n = 19
          -- in either cases we have n ≤ 19, which completes the proof
          rcases mul_eq_zero.mp eq <;> linarith
