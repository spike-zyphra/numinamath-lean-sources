import Mathlib

/- If all digits are zero, the resulting number is zero. -/
lemma Nat_ofdigits_replicate_zero_eq_zero (d : ℕ) (n : ℕ)
  : Nat.ofDigits d (List.replicate n 0) = 0 := by
    induction' n with h1 h2
    · norm_num
    · norm_num [List.replicate_succ, Nat.ofDigits_cons, h2]

/- If l contains some element a, [a] is an infix of a. -/
lemma List_infix_singleton (l : List ℕ) (a : ℕ) (h : a ∈ l)
  : [a] <:+: l := by
    -- proof by induction
    induction' l with b bs hh
    · norm_num at h
    · rcases List.mem_cons.mp h with rfl | mem
      · norm_num [List.infix_cons_iff]
      · exact List.infix_cons <| hh mem

/- If a list contains only 0 and 1, and contains a single 1, then the
   list can be constructed as [0, 0, ..., 0] ++ [1] ++ [0, 0, ..., 0]. -/
lemma List_exists_replicate_zero_append_of_zero_or_one_count {as : List ℕ} (h1 : ∀ a ∈ as, a = 0 ∨ a = 1) (h2 : as.count 1 = 1)
  : ∃ n m : ℕ, as = (List.replicate n 0) ++ [1] ++ (List.replicate m 0) := by
    -- [1] is infix of the list
    have a_infix : [1] <:+: as := by
      -- because it's contained in the list
      apply List_infix_singleton
      apply List.count_pos_iff.mp
      linarith

    -- the list consists of two lists with [a] in the middle
    obtain ⟨lr, ll, hl⟩ := a_infix
    exists lr.length, ll.length

    -- the total list has a single 1
    have count_one : (lr ++ [1] ++ ll).count 1 = 1 := by
      rw [hl]
      exact h2

    -- but then the two side lists has no 1
    simp only [List.append_assoc, List.singleton_append, List.count_append,
      List.count_cons_self] at count_one

    have lr_ones : lr.count 1  = 0 := by linarith
    have ll_ones : ll.count 1  = 0 := by linarith

    rw [List.count_eq_zero] at lr_ones ll_ones

    rw [←hl] at h1 ⊢
    congr
    -- both cases are pretty much the same
    all_goals
    · refine List.eq_replicate_of_mem ?_
      intro b bh
      have b_mem : b ∈ lr ++ [1] ++ ll := by
        norm_num
        tauto
      rcases h1 b b_mem with rfl | rfl
      · rfl
      · contradiction


lemma Nat_mul_eq_prime_pow {p a b n : ℕ} (hp : Nat.Prime p) (hab : a * b = p ^ n)
  : ∃ x y : ℕ, a = p ^ x ∧ b = p ^ y := by
    convert_to a * b = 1 * p ^ n at hab
    · ring

    have prime' : Prime p := Nat.prime_iff.mp hp
    obtain ⟨aa, bb, cc, dd, hh⟩ := mul_eq_mul_prime_pow prime' hab
    obtain ⟨rfl⟩ : cc = 1 := Nat.eq_one_of_mul_eq_one_right hh.2.1.symm
    obtain ⟨rfl⟩ : dd = 1 := Nat.eq_one_of_mul_eq_one_left hh.2.1.symm

    norm_num at hh
    exists aa, bb
    exact hh.2

lemma dvd_sub_iff_left {m n k : Nat} (hkn : k ≤ n) (h : m ∣ k) : m ∣ n - k ↔ m ∣ n := by
  rw (occs := [2]) [←Nat.sub_add_cancel hkn]
  exact Nat.dvd_add_iff_left h

/- If the difference of two powers of 3 is equal to 2, then one is 1 and the other 3. -/
lemma three_pow_sub_three_pow_eq_two {k1 k2 : ℕ} (lee : k2 ≤ k1) (h : 3 ^ k1 - 3 ^ k2 = 2)
  : k2 = 0 ∧ k1 = 1 := by
    -- 3 is prime
    have three_prime : Nat.Prime 3 := Nat.prime_three

    -- consider when k2 is positive
    by_cases hm : 1 ≤ k2
    -- then k1 is also positive
    · have k1_pos : 1 ≤ k1 := by omega

      -- so 3 divides 3 ^ k1 - 3 ^ k2
      have three_dvd : 3 ∣ 3 ^ k1 - 3 ^ k2 := by
        refine (dvd_sub_iff_left ?_ ?_).mpr ?_
        · gcongr
          omega
        · refine dvd_pow_self 3 ?_
          omega
        · refine dvd_pow_self 3 ?_
          omega
      -- but then 3 | 2
      rw [h] at three_dvd

      -- which is false
      have not_dvd : ¬3 ∣ 2 := by omega
      contradiction

    -- so k2 = 0
    have k2_eq : k2 = 0 := by omega

    subst k2_eq
    norm_num at h

    -- then k1 = 1
    have k1_eq : k1 = 1 := by
      rw [Nat.pow_eq_self_iff] at h
      exact h
      · omega

    tauto

/- 6. How many positive integers are a power of 4 and can be written in base 3 using only the digits 0 and 1, with 0 as many times as desired (even none) and 1 at most twice?
(A) 4
(B) 2
(C) 1
(D) 0
(E) Infinite. -/
theorem number_theory_135357 :
    Set.ncard {n : ℕ | ∃ k, n = 4 ^ k ∧ (∀ d ∈ Nat.digits 3 n, d = 0 ∨ d = 1) ∧ ((Nat.digits 3 n).filter (· = 1)).length ≤ 2} = 2
  := by
    -- we'll show that the only possible values are 1 and 4
    suffices h : {n : ℕ | ∃ k, n = 4 ^ k ∧ (∀ d ∈ Nat.digits 3 n, d = 0 ∨ d = 1) ∧ ((Nat.digits 3 n).filter (· = 1)).length ≤ 2} = {1, 4}
    · rw [h]
      norm_num

    ext n
    norm_num
    constructor
    -- we'll show the properties imply that n is 1 or 4
    · intro ⟨⟨k, kh⟩, cc, dd⟩
      -- consider when we have no digits
      by_cases hn : (Nat.digits 3 n).length = 0
      -- then n = 0
      · simp only [Nat.reduceLeDiff, List.length_eq_zero] at hn
        rw [Nat.digits_eq_nil_iff_eq_zero] at hn
        -- but there's no power of 4 which is equal to 0
        rw [hn, Eq.comm, pow_eq_zero_iff'] at kh
        norm_num at kh

      -- so we have a positive number of digits
      have len_pos : 0 < (Nat.digits 3 n).length := by omega

      -- let the first digit be a
      obtain ⟨a, as, ha⟩ := List.exists_cons_of_length_pos len_pos

      -- simplify
      rw [ha] at cc
      simp only [List.mem_cons, forall_eq_or_imp] at cc

      -- the first digit is either 0 or 1
      have a_case := cc.1

      -- 3 is prime
      have three_prime : Nat.Prime 3 := by decide

      -- consider possible values of a
      rcases a_case with h1 | h2
      -- consider when a is 0
      -- then 3 divides n
      · have three_dvd_n : 3 ∣ n := by
          rw [←Nat.ofDigits_digits 3 n, ha, Nat.ofDigits_cons, h1, zero_add]
          exact Nat.dvd_mul_right 3 (Nat.ofDigits 3 as)

        -- which means 3 divides 4 ^ k
        rw [kh] at three_dvd_n

        -- which means 3 divides 4
        have three_dvd_four := Nat.Prime.dvd_of_dvd_pow three_prime three_dvd_n

        -- but 3 does not divide 4, contradiction
        exact absurd three_dvd_four (by decide)
      -- now consider when a is 1
      · rw [ha, h2] at dd
        norm_num at dd
        -- then the rest of the digits has at most a single 1
        have rest_le : (as.filter (· = 1)).length ≤ 1 := by linarith

        -- consider the two cases
        interval_cases hh : (as.filter (· = 1)).length
        -- when there are no ones in the rest of the digits
        · simp only [List.length_eq_zero, List.filter_eq_nil_iff, decide_eq_true_eq] at hh
          -- so all the rest of the digits are 0
          have as_eq_zero : ∀ a ∈ as, a = 0 := by
            intro a ah
            have one_or_zero := cc.2 a ah
            have not_zero := hh a ah
            tauto

          have as_eq_replicate : as = List.replicate (as.length) 0 := List.eq_replicate_iff.mpr ⟨rfl, as_eq_zero⟩

          -- so n is 0000001
          have n_eq : n = Nat.ofDigits 3 (a :: List.replicate (as.length) 0) := by
            rw [←Nat.ofDigits_digits 3 n, ←as_eq_replicate, ha]

          -- then we have that n = a = 1
          rw [Nat.ofDigits_cons, Nat_ofdigits_replicate_zero_eq_zero] at n_eq
          norm_num [h2] at n_eq

          -- which is a valid solution
          tauto
        -- when there are is a single one in the rest of the digits
        -- i.e. if we count the number of ones in the rest of the digits we get 1
        · rw [List.filter_eq, List.length_replicate] at hh

          -- so we can write the rest of the digits as 000..00100..000
          obtain ⟨nn, mm, hh⟩ := List_exists_replicate_zero_append_of_zero_or_one_count cc.2 hh

          -- so we know that n = 1 + 3 * 3 ^ nn = n, for some nn
          have n_eq : 1 + 3 * 3 ^ nn = n := by
            rw [←Nat.ofDigits_digits 3 n, ha, hh, Nat.ofDigits_cons, h2, Nat.ofDigits_append,
              Nat_ofdigits_replicate_zero_eq_zero]
            norm_num
            have one_eq : [1] = Nat.digits 3 1 := by norm_num
            rw [one_eq, ←Nat.digits_base_pow_mul, Nat.ofDigits_digits]
            norm_num
            · omega
            · omega

          -- then we have 1 + 3 ^ (nn + 1) = 4 ^ k
          replace n_eq : 1 + 3 ^ (nn + 1) = n := by
            ring_nf
            linarith
          rw [kh] at n_eq

          -- we have that 4 ^ k = 2 ^ k * 2 ^ k
          have four_pow_eq : 4 ^ k = 2 ^ k * 2 ^ k := by
            ring_nf
            rw [Nat.pow_mul']
            norm_num

          -- so 3 ^ (nn + 1) = 2 ^ k * 2 ^ k - 1
          rw [four_pow_eq] at n_eq

          apply_fun (· - 1) at n_eq
          norm_num at n_eq

          -- which means (2 ^ k + 1) * (2 ^ k - 1) = 3 ^ (nn + 1)
          have three_pow_eq : (2 ^ k + 1) * (2 ^ k - 1) = 3 ^ (nn + 1) := by
            convert n_eq.symm using 1
            · exact (mul_self_tsub_one (2 ^ k)).symm

          -- so (2 ^ k + 1) and (2 ^ k - 1) are powers of 3, with exponents k1 and k2
          obtain ⟨k1, k2, k1h, k2h⟩ := Nat_mul_eq_prime_pow three_prime three_pow_eq

          -- clearly k2 ≤ k2
          have k2_le_k1 : k2 ≤ k1 := by
            have poss : 1 < 3 := by omega
            rw [←Nat.pow_le_pow_iff_right poss]
            rw [←k1h, ←k2h]
            simp only [tsub_le_iff_right]
            omega

          -- their difference is 2
          have pows_diff : 3 ^ k1 - 3 ^ k2 = 2 := by
            rw [←k1h, ←k2h]
            rw [add_tsub_tsub_cancel]
            exact Nat.one_le_two_pow

          -- but then the only possible values are k1 = 1 and k2 = 0
          obtain ⟨rfl, rfl⟩ := three_pow_sub_three_pow_eq_two k2_le_k1 pows_diff

          -- so 2 ^ k = 2
          norm_num at k2h

          -- so k = 1
          have k_eq : k = 1 := by
            simpa only [Nat.one_lt_ofNat, Nat.pow_eq_self_iff] using k2h

          -- then n = 4 ^ 1 = 4
          subst k_eq
          norm_num at kh

          -- as desired
          tauto

    -- then we show that 1 and 4 are valid solutions
    · rintro (eq_one | eq_four)
      · norm_num [eq_one]
        -- 1 is a 0th power of 4
        exists 0
      · norm_num [eq_four]
        -- 4 is a 1th power of 4
        exists 1