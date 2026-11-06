import Mathlib

/- # Problem 2.

In-1 A 2022-digit natural number is guessed, any two adjacent digits of which (arranged in the same order) form a two-digit number that is divisible either by 19 or by 23. The guessed number starts with the digit 4. What digit does it end with? -/
theorem number_theory_205094 (n : ℕ) (h₁ : (Nat.digits 10 n).length = 2022)
  (h₂ : List.Chain' (fun a b => 19 ∣ Nat.ofDigits 10 [a, b] ∨ 23 ∣ (Nat.ofDigits 10 [a, b])) (Nat.digits 10 n) )
  (h₃ : (Nat.digits 10 n).getLast (List.ne_nil_of_length_eq_add_one h₁) = 4) :
  (Nat.digits 10 n)[0]! = 6 ∨ (Nat.digits 10 n)[0]! = 8 := by
    -- Let f be the digits in big-endian order
    let f : ℕ → ℕ := fun i => (Nat.digits 10 n).reverse[i]!

    -- Then we want to find the digit at f 2021
    have last_digit_eq : (Nat.digits 10 n)[0]! = f 2021
    · unfold f
      simp only [List.getElem!_eq_getElem?_getD, Nat.default_eq_zero]
      rw [List.getElem?_reverse, h₁]
      · rw [h₁]
        exact Nat.lt_add_one 2021
    rw [last_digit_eq]

    -- Digits are less than 10
    have digit_le_ten : ∀ x, f x < 10
    · intro x
      unfold f
      by_cases h : x < (Nat.digits 10 n).length
      · rw [getElem!_pos]
        rw [List.getElem_reverse]
        exact @Nat.digits_lt_base 10 n _ (by linarith) (List.getElem_mem (by omega))
        rw [List.length_reverse]
        exact h
      · suffices hh : (Nat.digits 10 n).reverse[x]! = 0
        · rw [hh]
          omega
        · simp only [Nat.reduceLeDiff, List.getElem!_eq_getElem?_getD, Nat.default_eq_zero]
          rw [LawfulGetElem.getElem?_def]
          simp only [Nat.reduceLeDiff, List.length_reverse, h, ↓reduceDIte, Option.getD_none]

    -- Let's look at pairs of digits
    let f_pair : ℕ → ℕ := fun i => Nat.ofDigits 10 [f (i+1), f i]

    -- Then either 19 divides it or 23 divides it
    have f_pair_prop : ∀ x, x < 2021 → 19 ∣ f_pair x ∨ 23 ∣ f_pair x
    · intro x xh
      rw [←List.reverse_reverse (Nat.digits 10 n)] at h₂
      have yeah := List.chain'_iff_get.mp (List.chain'_reverse.mp h₂) x
        (by { rw [List.length_reverse, h₁]; exact xh })
      simp only [flip, List.get_eq_getElem, Nat.reduceLeDiff, List.getElem_reverse] at yeah
      unfold f_pair f
      rw [getElem!_pos, getElem!_pos, List.getElem_reverse, List.getElem_reverse]
      · exact yeah
      all_goals
      · rw [List.length_reverse]
        omega

    -- Zeros are preceded by zeroes
    have f_zero_before : ∀ x, x < 2021 → f (x+1) = 0 → f x = 0
    · intro xx xh xhh
      have yess := f_pair_prop xx xh
      unfold f_pair at *
      rw [xhh] at yess
      have le_ten := digit_le_ten xx
      simp only [Nat.reduceLeDiff, Nat.ofDigits_cons, Nat.ofDigits_nil,
        mul_zero, add_zero, zero_add] at yess
      omega

    -- First digit is 4
    have f_at_zero : f 0 = 4
    · unfold f
      rw [getElem!_pos, List.getElem_reverse]
      · convert h₃
        simp only [Nat.reduceLeDiff, tsub_zero]
        apply List.getElem_length_sub_one_eq_getLast
      · rw [List.length_reverse]
        exact Nat.lt_of_sub_eq_succ h₁

    -- So we don't have any zeros in the number
    have f_not_zero : ∀ x, x < 2022 → f x ≠ 0
    · intro xx xxh
      induction xx with
      | zero =>
      · rw [f_at_zero]
        exact (Nat.zero_ne_add_one 3).symm
      | succ x xh =>
      · by_contra hh
        exact (xh (by omega)) (f_zero_before x (by omega) hh)

    -- Then we have bounds on the pair of digits
    have f_pairs_bounds : ∀ {x}, x < 2021 → (10 ≤ f_pair x ∧ f_pair x ≤ 99)
    · intro x xh
      unfold f_pair
      rw [Nat.ofDigits_cons, Nat.ofDigits_singleton]
      have := f_not_zero x (Nat.lt_succ_of_lt xh)
      have := f_not_zero (x+1) (Nat.add_lt_of_lt_sub xh)
      have := digit_le_ten x
      have := digit_le_ten (x+1)
      omega

    -- Two digit numbers divisible by 19
    have div_19 : ∀ {n}, 10 ≤ n → n ≤ 99 → 19 ∣ n → n ∈ ({19, 38, 57, 76, 95} : Finset ℕ) := by decide

    -- Two digit numbers divisible by 23
    have div_23 : ∀ {n}, 10 ≤ n → n ≤ 99 → 23 ∣ n → n ∈ ({23, 46, 69, 92} : Finset ℕ) := by decide

    -- Then we know that adjacent digits are from a finite set
    have f_pair_digits : ∀ x, x < 2021 → f_pair x ∈ ({19, 38, 57, 76, 95} ∪ {23, 46, 69, 92} : Finset ℕ)
    · intro ii ih
      have ⟨ll, uu⟩ := f_pairs_bounds ih
      cases f_pair_prop ii ih with
      | inl h => exact Finset.mem_union_left {23, 46, 69, 92} (div_19 ll uu h)
      | inr h => exact Finset.mem_union_right {19, 38, 57, 76, 95} (div_23 ll uu h)

    -- As pairs
    have f_pairs : ∀ i, i < 2021 →
    (f i = 1 ∧ f (i + 1) = 9
      ∨ f i = 3 ∧ f (i + 1) = 8
      ∨ f i = 5 ∧ f (i + 1) = 7
      ∨ f i = 7 ∧ f (i + 1) = 6
      ∨ f i = 9 ∧ f (i + 1) = 5
      ∨ f i = 2 ∧ f (i + 1) = 3
      ∨ f i = 4 ∧ f (i + 1) = 6
      ∨ f i = 6 ∧ f (i + 1) = 9
      ∨ f i = 9 ∧ f (i + 1) = 2)
    · intro i ih
      have huehue := f_pair_digits i ih
      unfold f_pair at huehue
      rw [Nat.ofDigits_cons] at huehue
      simp only [Finset.union_insert, Finset.insert_union, Nat.ofDigits_singleton,
        Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at huehue
      have f_one := digit_le_ten i
      have f_one' := digit_le_ten (i + 1)
      -- Check each case manually
      rcases huehue with p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9
      { (iterate 5 right); left ; omega }
      { (iterate 6 right); left ; omega }
      { (iterate 7 right); left ; omega }
      {                    left ; omega }
      { (iterate 1 right); left ; omega }
      { (iterate 2 right); left ; omega }
      { (iterate 3 right); left ; omega }
      { (iterate 4 right); left ; omega }
      { (iterate 8 right)       ; omega }

    -- If a digit is 4, next digit is 6
    have f_4 : ∀ {i}, i < 2021 → f i = 4 → f (i + 1) = 6
      := @fun ii ih i4 => by simpa [i4] using f_pairs ii ih
    -- If a digit is 6, next digit is 9
    have f_six : ∀ {i}, i < 2021 → f i = 6 → f (i + 1) = 9
      := @fun ii ih i4 => by simpa [i4] using f_pairs ii ih
    -- If a digit is 9, next digit is 5 or 2
    have f_nine : ∀ {i}, i < 2021 → f i = 9 → (f (i + 1) = 5 ∨ f (i + 1) = 2)
      := @fun ii ih i4 => by simpa [i4] using f_pairs ii ih
    -- If a digit is 5, next digit is 7
    have f_five : ∀ {i}, i < 2021 → f i = 5 → f (i + 1) = 7
      := @fun ii ih i4 => by simpa [i4] using f_pairs ii ih
    -- If a digit is 7, next digit is 6
    have f_seven : ∀ {i}, i < 2021 → f i = 7 → f (i + 1) = 6
      := @fun ii ih i4 => by simpa [i4] using f_pairs ii ih
    -- If a digit is 2, next digit is 3
    have f_two : ∀ {i}, i < 2021 → f i = 2 → f (i + 1) = 3
      := @fun ii ih i4 => by simpa [i4] using f_pairs ii ih
    -- If a digit is 3, next digit is 8
    have f_three : ∀ {i}, i < 2021 → f i = 3 → f (i + 1) = 8
      := @fun ii ih i4 => by simpa [i4] using f_pairs ii ih

    -- No digit is 8, except possibly the last digit
    have f_not_8: ∀ {i}, i < 2021 → f i ≠ 8
    · intro ii ih
      by_contra h
      simpa only [h, OfNat.ofNat_ne_one, false_and, Nat.reduceEqDiff, Nat.succ_ne_self,
        or_self] using f_pairs ii ih

    -- A 9 digit has two possible continuations
    have f_nine_cont : ∀ {i}, i < 2019 → f i = 9 → (f (i + 3) = 6 ∨ f (i + 3) = 8)
    · intro ii ih ihh
      cases' f_nine (by omega) ihh with ha hb
      · have yoo1 := f_five (by omega) ha
        have yoo2 := f_seven (by omega) yoo1
        exact Or.inl yoo2
      · have yoo1 := f_two (by omega) hb
        have yoo2 := f_three (by omega) yoo1
        exact Or.inr yoo2

    -- The digits are semiperiodic (except for the end)
    have semi_periodic : ∀ {i}, (2 + i*4) < 2022 → f (2 + i*4) = 9
    · intro ii ih
      induction ii with
      | zero =>
      · simp only [zero_mul, add_zero]
        have f_at_one : f 1 = 6 := f_4 (Nat.zero_lt_succ 2020) (f_at_zero)
        exact f_six (Nat.one_lt_succ_succ 2019) f_at_one
      | succ jj jh =>
      · have yeah := jh (by omega)
        cases' f_nine_cont (by omega) yeah with ha hb
        · have yoo3 := f_six (by omega) ha
          ring_nf at yoo3 ⊢
          exact yoo3
        · exact False.elim ((f_not_8 (by omega)) hb)

    -- If the last digit is 3 steps after a 9 then there's two possible values
    apply f_nine_cont (Nat.lt_add_one 2018)

    -- And because it's semiperiodic we know that it's a 9, so we're done
    convert_to f (2 + 504*4) = 9
    exact semi_periodic (Nat.lt_of_sub_eq_succ rfl)