import Mathlib

/- Which is the smallest positive integer divisible by 28, whose decimal representation ends in 28, and the sum of whose digits is 28? -/
theorem number_theory_221375 :
    IsLeast {n | 0 < n ∧ 28 ∣ n ∧ (Nat.digits 10 n).headI = 8 ∧ (Nat.digits 10 n).tail.headI = 2 ∧
      (Nat.digits 10 n).sum = 28} 18928 := by

      constructor
      · -- first we show that n = 18928 is a solution, this is routine.
        simp
        norm_num

      -- now we show that n = 18928 is the least solution.
      -- consider any solution n, such that n > 0, 28 ∣ n, last digit of n is 8,
      -- last but one digit of n is 2, and the sum of digits of n is 28.
      rintro n ⟨n_pos, n_dvd_by_28, n_last_8, n_pre_last_2, n_sum_28⟩

      -- 1. we show that n % 100 = 28

      -- 1.1. we show that n % 10 = 8, as the last digit is 8
      have : n % 10 = 8 := by simp_all

      -- 1.2. we show that (n / 10) % 10 = 2, as the last but one digit is 2
      have : (Nat.digits 10 (n / 10)) = (Nat.digits 10 n).tail := by
        simp [Nat.digits_eq_cons_digits_div, *]
      have : (Nat.digits 10 (n / 10)).headI = 2 := by rw [this]; assumption
      have : n / 10 > 0 := by
        by_contra! h
        have : n / 10 = 0 := by exact Nat.eq_zero_of_le_zero h
        have : (Nat.digits 10 (n / 10)) = [] := by exact Nat.digits_eq_nil_iff_eq_zero.mpr this
        simp_all
      have : (n / 10) % 10 = 2 := by simp_all

      -- 1.3. combining the above results, we derive n % 100 = 28.
      have : n % 100 = 28 := by
        rw [show 100 = 10 * 10 by norm_num, Nat.mod_mul]
        simp_all

      -- 2. so we have n = 100 * B + 28, where B = ⌊n / 100⌋.
      let B := n / 100
      have h_n_B : n = 100 * B + 28 := by
        unfold B
        rw [← this]
        exact Eq.symm (Nat.div_add_mod n 100)

      -- 3. we show that 28 ∣ 100 * B = n - 28, as 28 ∣ n.
      have : 28 ∣ (100 * B) := by
        rw [h_n_B] at n_dvd_by_28
        exact Nat.dvd_add_self_right.mp n_dvd_by_28

      -- 4. we deduce from 3. that B is a multiple of 7
      have B_dvd_by_7 : 7 ∣ B := by
        rw [show 28 = 4 * 7 by norm_num, show 100 = 4 * 25 by norm_num] at this
        have : 7 ∣ 25 * B := by
          obtain ⟨c, hc⟩ := dvd_def.mp this
          have : 25 * B = 7 * c := by
            rw [Nat.mul_assoc, Nat.mul_assoc] at hc
            apply Nat.mul_left_cancel (n := 4) (by norm_num) hc
          exact Dvd.intro c (id (Eq.symm this))
        have prime_7 : Nat.Prime 7 := by norm_num
        have := (Prime.dvd_mul (show Prime 7 by exact Nat.prime_iff.mp prime_7)).mp this
        have : ¬ 7 ∣ 25 := by exact (Nat.Prime.coprime_iff_not_dvd prime_7).mp rfl
        simp_all

      -- 5. the sum of digits of n is n % 9 = 28.
      have : n ≡ 28 [MOD 9] := by
        rw [← n_sum_28]
        exact Nat.modEq_nine_digits_sum n
      rw [h_n_B] at this

      -- 6. so n - 28 = 100 * B is a multiple of 9.
      have : 100 * B ≡ 0 [MOD 9] := by
        nth_rw 2 [show 28 = 0 + 28 by norm_num] at this
        exact Nat.ModEq.symm (Nat.ModEq.add_right_cancel' 28 (id (Nat.ModEq.symm this)))

      have : 100 * B ≡ B [MOD 9] := by nth_rw 2 [show B = 1 * B by ring]; exact Nat.ModEq.mul rfl rfl

      have : B ≡ 0 [MOD 9] := by trans 100 * B; symm; all_goals assumption

      -- 7. we deduce that B is a multiple of 9, as 9 and 100 are co-primes.
      have B_dvd_by_9: 9 ∣ B := by exact Nat.dvd_of_mod_eq_zero this

      -- 8. we deduce from 4. and 7. that B is a multiple of 63, as 7 and 9 are co-primes.
      have B_dvd_by_63 : 63 ∣ B := by
        rw [show 63 = 7 * 9 by norm_num]
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl B_dvd_by_7 B_dvd_by_9

      -- 9. therefore, we can write B = 63 * k
      obtain ⟨k, hk⟩ := dvd_def.mp B_dvd_by_63

      -- 10. we show that k ≥ 3, as otherwise the sum of digits of n is not 28
      have k_ge_3 : k ≥ 3 := by
        by_contra! h
        interval_cases k
        all_goals simp_all

      -- finally, as k ≥ 3, we have B ≥ 63 * 3 and n ≥ 100 * (63 * 3) + 28 = 18928.
      calc
        n = 100 * B + 28 := by exact h_n_B
        _ = 100 * (63 * k) + 28 := by rw [hk]
        _ ≥ 100 * (63 * 3) + 28 := by rel [k_ge_3]
        _ = 18928 := by rfl
