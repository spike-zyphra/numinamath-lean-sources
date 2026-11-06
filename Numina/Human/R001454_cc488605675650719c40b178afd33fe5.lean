import Mathlib


def is_double_number (n : ℕ) := ∃ k, n = k * 10 ^ (Nat.digits 10 k).length + k

/- 25. (GBR 1) A positive integer is called a double number if its decimal representation consists of a block of digits, not commencing with 0 , followed immediately by an identical block. For instance, 360360 is a double number, but 36036 is not. Show that there are infinitely many double numbers that are perfect squares. -/
theorem number_theory_24148 :
    ∀ N, ∃ n, IsSquare n ∧ is_double_number n ∧ n > N := by

  -- we claim 7^2 divide 10^21 + 1
  have h1: 7^2 ∣ 10^21 + 1 := by
    zify
    -- 7 divide 10^3 + 1
    obtain ⟨a, ha⟩: ∃ a, (10:ℤ)^3 = (-1 + 7*a) := by
      use 143
      norm_num
    have h1: (10:ℤ)^21 = ((10:ℤ)^3)^7 := by
      rw [← pow_mul]
    rw [h1, ha]
    -- use binomial theorem, expand
    rw [add_pow, Finset.sum_range_succ,
    Finset.sum_range_succ, add_assoc, add_assoc]
    refine Dvd.dvd.add ?_ ?_
    · apply Finset.dvd_sum ?_
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [mul_assoc]
      apply Dvd.dvd.mul_left ?_
      by_cases ieq: i = 0
      · apply Dvd.dvd.mul_right ?_
        rw [ieq, mul_pow]
        apply Dvd.dvd.mul_right ?_
        exact Int.dvd_of_emod_eq_zero rfl
      · have hh1: 7 ∣ (7*a)^(7-i) := by
          apply Dvd.dvd.pow ?_ (by omega)
          exact Int.dvd_mul_right 7 a
        have hh2: (7:ℤ) ∣ Nat.choose 7 i := by
          norm_cast
          refine Nat.Prime.dvd_choose_self (by norm_num) ?_ ?_
          <;> omega
        rw [pow_two]
        exact Int.mul_dvd_mul hh1 hh2
    · simp only [Int.reducePow, Int.reduceNeg, Nat.reduceSub, pow_one, one_mul,
      Nat.choose_succ_self_right, Nat.reduceAdd, Nat.cast_ofNat,
      tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      neg_add_cancel, add_zero]
      ring_nf
      apply Int.dvd_mul_left

  -- then we claim for any odd n, 7^2 divide 10^(21n) + 1
  have h2 {n:ℕ} (hn: Odd n): 7^2 ∣ 10^(21*n) + 1 := by
    have: 10^21 + 1 ∣ (10^21)^n + 1^n := by
      apply hn.nat_add_dvd_pow_add_pow
    rw [one_pow, ← pow_mul] at this
    apply h1.trans this

  intro N
  -- make it an odd number
  have h3: Odd (2*N+1) := odd_two_mul_add_one N
  have h4: 10^(21*(2*N+1)) > N := by
    have: 10^(21*(2*N+1)) > 21*(2*N+1) := by
      apply Nat.lt_pow_self (by norm_num)
    apply lt_trans ?_ this
    linarith only
  -- we claim 3^2/7^2 (10^(21n')+1)^2 is the very number we want.
  specialize h2 h3
  rcases h2 with ⟨m, hm⟩
  have mpos: 0 < m := by
    suffices m ≠ 0 by omega
    rintro rfl
    simp at hm
  use (m*3^2) * (10^(21*(2*N+1)) + 1)
  split_ands
  · rw [hm]
    use (m*3*7)
    ring
  · -- it's a double number, since 3^2/7^2 10^(21n'+1) has 21n' digits.
    rw [mul_add_one]
    use (m*3^2)
    suffices (Nat.digits 10 (m*9)).length = 21*(2*N+1) by
      simp [this]
    rw [Nat.digits_len 10 _ (by norm_num) (by omega)]
    have: Nat.log 10 (m*9) = 21*(2*N+1) - 1 := by
      have: 21*(2*N+1) - 1 ≠ 0 := by omega
      rw [Nat.log_eq_iff (by simp [this])]
      replace: 1 < 21*(2*N+1) := by omega
      constructor
      · suffices 10 * (10^(21*(2*N+1)-1)) ≤ 10 * (m*9) by
          apply (mul_le_mul_iff_of_pos_left (by norm_num)).mp this
        rw [← pow_succ', Nat.sub_add_cancel this.le]
        suffices 7^2*m ≤ 10*(m*9) by
          apply le_trans ?_ this
          rw [← hm]
          simp
        linarith only
      · rw [Nat.sub_add_cancel this.le]
        suffices m*9+1 < 10^(21*(2*N+1)) + 1 by
          simpa only [gt_iff_lt, add_lt_add_iff_right] using this
        rw [hm]
        linarith only [mpos]
    rw [this, Nat.sub_add_cancel]
    omega
  · apply h4.trans ?_
    have kpos: 0 < 10^(21*(2*N+1)) := by simp
    generalize 10^(21*(2*N+1)) = k at kpos ⊢
    refine Nat.lt_add_right _ ?_
    refine (Nat.lt_mul_iff_one_lt_left kpos).mpr ?_
    omega