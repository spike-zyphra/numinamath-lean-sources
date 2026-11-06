import Mathlib

/- if n is a number of three digits, then its digits is as follows -/
lemma l_digits_three_digit_number {n:ℕ} (nge: n ≥ 100) (nle: n ≤ 999):
  Nat.digits 10 n = [n % 10, (n / 10 % 10), n / 100] := by
  have h1: 1 < 10 := by norm_num
  have h2: 0 < n := by linarith only [nge]
  have h3: 0 < n / 10 := by
    refine Nat.div_pos ?_ (by norm_num)
    linarith only [nge]
  have h4: 0 < n / 10 / 10 := by
    rw [Nat.div_div_eq_div_mul]
    refine Nat.div_pos ?_ (by norm_num)
    linarith only [nge]
  have h5: n / 10 / 10 / 10 = 0 := by
    simp only [Nat.div_div_eq_div_mul]
    refine Nat.div_eq_of_lt ?_
    exact Order.lt_add_one_iff.mpr nle
  rw [Nat.digits_def' h1 h2,
  Nat.digits_def' h1 h3, Nat.digits_def' h1 h4,
  h5, Nat.div_div_eq_div_mul]
  simp only [Nat.reduceMul, Nat.reduceLeDiff, Nat.digits_zero,
  List.cons.injEq, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
  Nat.reduceAdd, and_true, true_and, gt_iff_lt]
  refine Nat.div_lt_of_lt_mul ?_
  exact Order.lt_add_one_iff.mpr nle


/- 30.9. Find the largest three-digit number such that
the number minus the sum of its digits is a perfect square. -/
theorem number_theory_214653:
  IsGreatest {n:ℕ | n ∈ Finset.Icc 100 999 ∧
    IsSquare (n - (Nat.digits 10 n).sum)} 919 := by

  rw [IsGreatest, upperBounds]
  constructor

  · -- verify 919 satisfy the condition
    have: IsSquare 900 := by
      use 30
    simp [this]

  · -- prove 919 is an upper bound.
    simp only [Finset.mem_Icc, Nat.reduceLeDiff,
    Set.mem_setOf_eq, and_imp]
    intro n nge nle hsq

    -- consider digits of n.
    have h1 := l_digits_three_digit_number nge nle
    have h2: n = 100 * (n/100) + 10 * (n/10 % 10) + n % 10 := by
      nth_rw 1 [← Nat.ofDigits_digits 10 n, h1]
      simp only [Nat.ofDigits, Nat.cast_id, mul_zero, add_zero]
      ring
    -- each digit ≤ 9
    have h3: n % 10 < 10 := Nat.mod_lt n (by norm_num)
    have h4: n / 10 % 10 < 10 := Nat.mod_lt _ (by norm_num)
    replace h3: n % 10 ≤ 9 := Order.lt_add_one_iff.mp h3
    replace h4: n / 10 % 10 ≤ 9 := Order.lt_add_one_iff.mp h4

    -- if hundreds-digit is not 9, then n obviously < 900 < 919.
    by_cases h5: n / 100 ≠ 9
    · have: n / 100 < 10 := by
        refine Nat.div_lt_of_lt_mul ?_
        exact Order.lt_add_one_iff.mpr nle
      replace: n / 100 ≤ 9 := Order.lt_add_one_iff.mp this
      replace := lt_of_le_of_ne this h5
      replace: n / 100 ≤ 8 := Order.lt_add_one_iff.mp this
      rw [h2]
      linarith only [h3, h4, this]
    push_neg at h5

    -- then fix hundreds_digit is 9, consider n - digits-sum is square
    -- (100a+10b+c) - (a+b+c) = 9 (11a+b)
    have h6: n - (Nat.digits 10 n).sum =
      9 * (11* (n/100) + (n/10 % 10)) := by
      nth_rw 1 [h2]
      refine (Nat.eq_sub_of_add_eq ?_).symm
      simp only [h1, List.sum_cons, List.sum_nil, add_zero]
      ring
    rw [h6, h5] at hsq

    -- 9 (99 + n/10 % 10) is square.
    -- 9 is square, so 99 + n/10 % 10 = 99,100,101,...,108 must be square.
    -- only possible answer is 100, or, n/10%10 = 1.
    replace hsq: n / 10 % 10 = 1 := by
      generalize (n / 10 % 10) = k at h4 hsq ⊢
      clear * - hsq h4
      revert hsq
      native_decide +revert

    -- then max of last digit is 9, n ≤ 919.
    rw [h2, hsq, h5]
    linarith only [h3]