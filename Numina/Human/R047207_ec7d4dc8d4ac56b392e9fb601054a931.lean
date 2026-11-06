import Mathlib

/- 11.36 Find a three-digit number that has the following property: when its digits are written in the same order in a non-decimal base, the number is twice the original number:
(Polish Mathematical Olympiad, 1961) -/
theorem number_theory_158450 :
  ∃ c x y z n, Nat.digits 10 n = [z, y, x] ∧ 2 * n = Nat.ofDigits c [z, y, x]  := by
    -- We just need to find solutions to the equation 2 * (100 * x + 10 * y + z) = x * c ^ 2 + y * c + z
    convert_to ∃ c x y z, z < 10 ∧ y < 10 ∧ 1 ≤ x ∧ x < 10 ∧ 2 * (100 * x + 10 * y + z) = x * c ^ 2 + y * c + z using 0
    · refine exists₄_congr ?_
      intro c x y z
      constructor
      · intro ⟨n, nh1, nh2⟩
        -- x y z are digits of n
        have mems : x ∈ Nat.digits 10 n ∧ y ∈ Nat.digits 10 n ∧ z ∈ Nat.digits 10 n := by
          rw [nh1]
          simp only [List.mem_cons, List.mem_singleton, or_true, true_or, and_self]

        -- so they are all less than 10
        refine ⟨Nat.digits_lt_base (by linarith) mems.2.2, ?_⟩
        refine ⟨Nat.digits_lt_base (by linarith) mems.2.1, ?_⟩
        refine ⟨?_, Nat.digits_lt_base (by linarith) mems.1, ?_⟩
        -- and 1 ≤ x, because x is the first digit, which means it's not 0
        · refine Nat.one_le_iff_ne_zero.mpr ?_
          have non_empty : Nat.digits 10 n ≠ [] := List.ne_nil_of_mem mems.2.2
          convert_to (Nat.digits 10 n).getLast non_empty ≠ 0
          · rw [List.getLast_congr _ _ nh1]
            exact Nat.add_zero x
            exact List.cons_ne_nil z [y, x]
          apply Nat.getLast_digit_ne_zero
          by_contra hh
          rw [hh] at nh1
          simp only [Nat.reduceLeDiff, Nat.digits_zero, List.nil_eq, reduceCtorEq] at nh1
        -- and the equation holds because we have equality of Nat.ofDigits
        rw [←Nat.ofDigits_digits 10 n, Nat.ofDigits_eq_foldr, Nat.ofDigits_eq_foldr, nh1] at nh2
        simp only [Nat.cast_id, List.foldr_cons, List.foldr_nil, mul_zero, add_zero] at nh2
        linarith
      -- equality of Nat.ofDigits holds because of the equation
      · intro ⟨zh, yh, xh1, xh2, eh⟩
        refine ⟨Nat.ofDigits 10 [z, y, x], ?_⟩
        rw [Nat.digits_ofDigits]
        simp only [Nat.digits_ofDigits, true_and, Nat.ofDigits_eq_foldr, Nat.cast_id,
          List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
        · linarith
        · linarith
        · simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
          refine ⟨zh, yh, xh2, ?_⟩
          simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
        · simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self,
            List.getLast_singleton, forall_const]
          exact Nat.not_eq_zero_of_lt xh1

    -- c must be 15
    convert_to ∃ x y z, z < 10 ∧ y < 10 ∧ 1 ≤ x ∧ x < 10 ∧ 2 * (100 * x + 10 * y + z) = x * 15 ^ 2 + y * 15 + z using 0
    · constructor
      · intro ⟨c, x, y, z, zh, yh, xh1, xh2, eh⟩
        -- if c ≤ 14 then the equation cannot work
        by_cases hh : c ≤ 14
        · interval_cases c <;> linarith only [eh, xh1]
        -- if 16 ≤ c, we have an equation equal to zero which is also less than 0
        by_cases hh2 : 16 ≤ c
        -- consider the equation as an equality of integers
        · zify at eh
          have eq_int : (200 - (c : ℤ) ^ 2) * (x : ℤ) + (20 - (c : ℤ)) * (y : ℤ) + (z : ℤ) = 0 := by linarith
          have x_coeff : (200 - (c : ℤ) ^ 2) ≤ -56 := by nlinarith
          have x_term : (200 - (c : ℤ) ^ 2) * (x : ℤ) ≤ -56 * (x : ℤ) := by nlinarith
          have y_term : (20 - (c : ℤ)) * (y : ℤ) ≤ 4 * (y : ℤ) := by nlinarith
          linarith
        -- so c = 15
        have c_eq_15 : c = 15 := by linarith
        exact ⟨x, y, z, zh, yh, xh1, xh2, c_eq_15 ▸ eh⟩
      · intro ⟨x, y, z, zh, yh, xh1, xh2, eh⟩
        exact ⟨15, x, y, z, zh, yh, xh1, xh2, eh⟩
    -- we see that x = 1, y = 5, z = 0 works
    refine ⟨1, 5, 0, ?_⟩
    simp only [Nat.ofNat_pos, Nat.reduceLT, le_refl, Nat.one_lt_ofNat, mul_one, Nat.reduceMul,
      Nat.reduceAdd, add_zero, Nat.reducePow, one_mul, and_self]