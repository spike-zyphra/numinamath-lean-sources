import Mathlib

/- ## Task A-2.3.

Determine all ordered triples $(m, n, p)$ where $m$ and $n$ are natural numbers, and $p$ is a prime number, for which the following holds:


$$

25^{n}+2 \cdot 5^{n}=p^{m}+8

$$
 -/
theorem number_theory_208684 (m n p : ℕ) (hp : Nat.Prime p)
    (h : 25^n + 2 * 5^n = p^m + 8) :
    (m, n, p) = (3, 1, 3)
  := by

    -- We can easily see that n = 0 doesn't work
    by_cases hn : n = 0
    · subst hn
      simp only [pow_zero, mul_one, Nat.reduceAdd, self_eq_add_left,
        AddLeftCancelMonoid.add_eq_zero, pow_eq_zero_iff', ne_eq, OfNat.ofNat_ne_zero,
        and_false] at h

    -- Expression for p ^ m
    have h'' : 25^n + 2 * 5^n - 8 = p ^ m
    · omega

    -- Split up left hand side into factors
    convert_to (5 ^ n - 2) * (5 ^ n + 4) = p ^ m at h''
    · ring_nf
      rw [Nat.sub_mul, Nat.sub_mul, ←Nat.mul_pow]
      simp only [Nat.reduceMul]
      rw [←Nat.sub_add_comm]
      congr 1
      ring_nf
      rw [←Nat.sub_add_comm]
      · omega
      · convert_to 5 ^ n * 2 ≤ (5*5) ^ n
        rw [Nat.mul_pow]
        simp only [Nat.ofNat_pos, pow_pos, mul_le_mul_left]
        calc 2
        _ ≤ 5 ^ 1 := by omega
        _ ≤ 5 ^ n := pow_right_mono₀ (by omega) (by omega)
      calc 8
        ≤ 5 ^ 1 * 4 := by omega
      _ ≤ 5 ^ n * 4 := Nat.mul_le_mul (pow_right_mono₀ (by omega) (by omega)) <| le_refl 4


    -- Then we can express the factors as powers of p
    -- e.g. p ^ a * p ^ b = p ^ m where a + b = m
    convert_to (5 ^ n - 2) * (5 ^ n + 4) = 1 * p ^ m at h''
    · omega

    obtain ⟨a, b, cc, dd, hb1, hb2, hb3, hb4⟩
      := mul_eq_mul_prime_pow (Nat.prime_iff.mp hp) h''
    have ⟨one_eq1, one_eq2⟩ := mul_eq_one.mp (hb2.symm)
    subst one_eq1
    subst one_eq2
    clear hb2
    rw [one_mul] at hb3 hb4

    -- We know that a < b
    have aa_lt_bb : a < b
    · have pow_yeah : p ^ a < p ^ b
      · rw [←hb3, ←hb4]
        omega
      exact (pow_lt_pow_iff_right₀ <| Nat.Prime.one_lt hp).mp pow_yeah

    -- and that a ≠ 0
    by_cases haa : a = 0
    · subst a
      have weird : 1 < 5 ^ n - 2
      · calc 1
        _ < 5 ^ 1 - 2 := by omega
        _ ≤ 5 ^ n - 2 := by
          apply Nat.sub_le_sub_right
          exact Nat.le_self_pow hn (5 ^ 1)
      exact False.elim <| (lt_self_iff_false 1).mp (pow_zero p ▸ hb3 ▸ weird)

    -- Then we have that p ^ b - p ^ a = 6, and factor out p ^ a
    have pows_eq_six : p ^ a * (p ^ (b - a) - 1) = 2 * 3
    · rw [Nat.mul_sub, ←Nat.pow_add]
      convert_to p ^ b - p ^ a = 6
      · congr <;> omega
      rw [←hb3, ←hb4]

      have two_le_pow : 2 ≤ 5 ^ n
      · calc 2
        _ ≤ 5 ^ 1 := by omega
        _ ≤ 5 ^ n := Nat.le_self_pow hn (5 ^ 1)

      simp only [two_le_pow, add_tsub_tsub_cancel, Nat.reduceAdd]

    -- Then p ^ a divides 2 * 3
    have dvd_v : p ^ a ∣ 2 * 3
    · rw [←pows_eq_six]
      exact Nat.dvd_mul_right (p ^ a) (p ^ (b - a) - 1)

    -- Then p ^ 2 divides 2 or 3
    have dvd_or : p ^ a ∣ 2 ∨ p ^ a ∣ 3
    · obtain ⟨pp, qq, ha, hb, hc⟩ := dvd_mul.mp dvd_v
      have pp_le : pp ≤ 2 := Nat.le_of_dvd (by tauto) ha
      have qq_le : qq ≤ 3 := Nat.le_of_dvd (by tauto) hb
      interval_cases qq
      · simp only [zero_dvd_iff, OfNat.ofNat_ne_zero] at hb
      · rw [mul_one] at hc
        exact Or.inl <| hc.symm ▸ ha
      · contradiction
      · interval_cases pp
        · simp only [zero_dvd_iff, OfNat.ofNat_ne_zero] at ha
        · simp only [one_mul] at hc
          rw [hc]
          tauto
        · apply_fun Nat.primeFactors at hc
          rw [Nat.primeFactors_prime_pow haa hp, Nat.Coprime.primeFactors_mul,
            Nat.Prime.primeFactors Nat.prime_three, Nat.Prime.primeFactors Nat.prime_two] at hc
          apply_fun Finset.card at hc
          simp only [Finset.card_singleton, Finset.disjoint_singleton_right, Finset.mem_singleton,
            Nat.reduceEqDiff, not_false_eq_true, Finset.card_union_of_disjoint, Nat.reduceAdd,
            OfNat.one_ne_ofNat] at hc
          decide

    -- Then p = 2, or p = 3 (and p ^ a = 3)
    have eq_two_or_three : p = 2 ∨ (p = 3 ∧ p ^ a = 3)
    · have lee : p ^ a ≤ 3
      · cases' dvd_or with p2 p3
        · exact Nat.le_succ_of_le <| Nat.le_of_dvd (by tauto) p2
        · exact Nat.le_of_dvd (by tauto) p3
      interval_cases hh : p ^ a
      · simp only [zero_dvd_iff, OfNat.ofNat_ne_zero, or_self] at dvd_or
      · convert_to p ^ a = 1 ^ a at hh
        · exact Eq.symm (Nat.one_pow a)
        have p_eq_one := Nat.pow_left_injective haa hh
        subst p_eq_one
        simp only [one_pow, tsub_self, mul_zero, Nat.reduceMul, OfNat.zero_ne_ofNat] at pows_eq_six
      · have yoyo := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hh
        exact Or.inl yoyo.1
      · have yoyo := (Nat.Prime.pow_eq_iff Nat.prime_three).mp hh
        exact Or.inr ⟨yoyo.1, rfl⟩

    -- Consider cases of p
    cases' eq_two_or_three with h2 h3
    -- If p = 2, then original equation has odd left hand side, and even right hand side
    · have ls : Odd (25 ^ n + 2 * 5 ^ n)
      · refine Nat.odd_add.mpr ?_
        simp only [even_two, Even.mul_right, iff_true]
        apply Odd.pow
        decide
      have rs : Even (p ^ m + 8)
      · rw [h2]
        refine Nat.even_add.mpr ?_
        have ee : Even 8 := by decide
        simp only [ee, iff_true]
        apply Nat.even_pow.mpr
        simp only [even_two, ne_eq, true_and]
        by_contra hh
        rw [hh] at hb1
        simp only [AddLeftCancelMonoid.add_eq_zero] at hb1
        exact absurd hb1.1 haa
      rw [h, ←Nat.not_even_iff_odd] at ls
      exact absurd rs ls
    -- If p = 3, then we have a solution
    · have ⟨ha1, ha2⟩ := h3
      have ⟨_, a_eq_one⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp ha2
      rw [ha2, a_eq_one, mul_comm] at pows_eq_six
      replace pows_eq_six := Nat.mul_right_cancel (by tauto) pows_eq_six
      simp only [Nat.pred_eq_succ_iff, Nat.reduceAdd] at pows_eq_six
      have eq_prime := (Nat.Prime.pow_eq_iff Nat.prime_three).mp pows_eq_six
      simp only [Nat.pred_eq_succ_iff, zero_add] at eq_prime
      rw [eq_prime.2, a_eq_one] at hb1
      simp only [Nat.reduceAdd] at hb1
      rw [ha2] at hb3
      have pow_eq_self : 5 ^ n = 5 := by omega
      have res := (Nat.Prime.pow_eq_iff Nat.prime_five).mp pow_eq_self

      -- Then we that m = 3, n = 1 and p = 3
      rw [←hb1, ha1, res.2]