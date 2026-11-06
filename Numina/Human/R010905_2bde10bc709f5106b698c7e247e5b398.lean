import Mathlib


/- [ Decimal numeral system ]

Prove that the product of the digits of any natural number greater than 9 is less than the number itself.

# -/
theorem number_theory_202501:
  ∀(n:ℕ), n > 9 → (Nat.digits 10 n).prod < n := by
  intro n hn
  -- n ≥ 10, digit length ≥ 2.
  have h1: (Nat.digits 10 n).length ≥ 2 := by
    by_contra!
    replace: (Nat.digits 10 n).length ≤ 1 := Nat.le_of_lt_succ this
    replace hn: n ≥ 10 := by exact hn
    have h: n < 10^(Nat.digits 10 n).length := by
      exact Nat.lt_base_pow_length_digits'
    absurd hn
    push_neg
    apply lt_of_lt_of_le h ?_
    nth_rw 3 [← pow_one 10]
    apply (Nat.pow_le_pow_iff_right (by norm_num)).mpr this

  have h1': Nat.digits 10 n ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    omega
  obtain ⟨k, kpos, hk⟩: ∃ (k: Fin (Nat.digits 10 n).length),
    ⟨0, (by omega)⟩ < k ∧
    (Nat.digits 10 n).length = k + 1 := by
    use ⟨(Nat.digits 10 n).length - 1, (by omega)⟩
    simp only [Nat.reduceLeDiff, Fin.mk_lt_mk, tsub_pos_iff_lt]
    omega
  have keq: (k:ℕ) = (Nat.digits 10 n).length - 1 := by
    omega

  -- single out most significant digit
  have h2: (Nat.digits 10 n) = (Nat.digits 10 n).take (k + 1) := by
    rw [← hk, List.take_length]
  rw [h2, List.prod_take_succ _ _ k.is_lt]

  -- product of remaining digits ≤ 9^k
  have h3: ((Nat.digits 10 n).take k).prod ≤ 9^(k:ℕ) := by
    nth_rw 2 [← List.length_take_of_le k.is_le']
    apply List.prod_le_pow_card
    intro i hi
    replace hi: i ∈ Nat.digits 10 n := List.mem_of_mem_take hi
    suffices i < 10 by exact Nat.le_of_lt_succ this
    exact Nat.digits_lt_base' hi
  replace h3: ((Nat.digits 10 n).take k).prod < 10^(k:ℕ) := by
    refine lt_of_le_of_lt h3 ?_
    apply (Nat.pow_lt_pow_iff_left ?_).mpr (by norm_num)
    exact Nat.not_eq_zero_of_lt kpos
  replace h3: ((Nat.digits 10 n).take k).prod *
    (Nat.digits 10 n)[k] < 10^(k:ℕ) * (Nat.digits 10 n)[k] := by
    refine Nat.mul_lt_mul_of_pos_right h3 ?_
    simp only [Nat.reduceLeDiff, Fin.getElem_fin,
    gt_iff_lt, keq]
    rw [List.getElem_length_sub_one_eq_getLast]
    refine Nat.zero_lt_of_ne_zero ?_
    refine Nat.getLast_digit_ne_zero 10 (by omega)

  -- and 10^k multiply most siginificant digit ≤ n
  have h4: 10^(k:ℕ) * (Nat.digits 10 n)[k] ≤ n := by
    rw [mul_comm (10^(k:ℕ)) _, ← Nat.le_div_iff_mul_le (by simp),
    Nat.self_div_pow_eq_ofDigits_drop _ _ (by norm_num)]
    rw [keq, List.drop_length_sub_one h1',
    ← List.get_length_sub_one (by omega)]
    simp [keq]

  -- done.
  exact lt_of_lt_of_le h3 h4