import Mathlib


/- Trouver tous les triplets d'entiers naturels non nuls $(a, b, c)$ tels que

$$
2021^{a}+4=3^{b} \times 5^{c}
$$ -/
theorem number_theory_604735 (a b c : ℕ) :
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ 2021^a + 4 = 3^b * 5^c ↔ (a, b, c) = (1, 4, 2) := by

  -- if n is odd, then n+2 and n-2 are coprime
  have co_odd_add2 {n:ℕ} (hn1: Odd n) (hn2: n ≥ 3): Nat.Coprime (n+2) (n-2) := by
    have: n+2 = (n-2) + 2^2 := by omega
    rw [this]
    refine Nat.coprime_self_add_left.mpr ?_
    refine Nat.Coprime.pow_left 2 ?_
    refine Nat.coprime_two_left.mpr ?_
    refine Nat.Odd.sub_even ?_ hn1 (by norm_num)
    linarith only [hn2]

  -- if 3^x 5^y = 45,  then x=2 and y = 1.
  -- since 45 = 3^2 x 5 and 3,5 are distince prime numbers
  have solve_eq1 {x y: ℕ} (h: 3^x * 5^y = 45): x = 2 ∧ y = 1 := by
    have h1: 3^x ∣ 45 := by
      rw [← h]
      apply Nat.dvd_mul_right
    replace h1: x < 3 := by
      by_contra!
      replace: 3^3 ∣ 3^x := Nat.pow_dvd_pow_iff_le_right'.mpr this
      replace: 3^3 ∣ 45 := Nat.dvd_trans this h1
      norm_num at this
    have h2: 5^y ∣ 45 := by
      rw [← h]
      apply Nat.dvd_mul_left
    replace h2: y < 2 := by
      by_contra!
      replace: 5^2 ∣ 5^y := Nat.pow_dvd_pow_iff_le_right'.mpr this
      replace: 5^2 ∣ 45 := Nat.dvd_trans this h2
      norm_num at this
    obtain (rfl | rfl) : y = 0 ∨ y = 1 := by omega
    · simp only [pow_zero, mul_one] at h
      -- impossible for 3^x = 45
      have: 3^x < 3^3 := by
        apply (Nat.pow_lt_pow_iff_right (by norm_num)).mpr h1
      norm_num [h] at this
    · simp only [pow_one] at h
      have: 3^x = 3^2 := by linarith only [h]
      refine ⟨?_, (by simp)⟩
      apply (pow_right_inj₀ (by norm_num) (by norm_num)).mp this

  -- if x ≥ 2, then 47^x > 43^x + 4
  have ineq1 {x: ℕ} (hx: x ≥ 2): 47^x > 43^x + 4 := by
    induction' x,hx using Nat.le_induction with x hx ih
    · norm_num
    · simp only [pow_succ]
      have h1: 47^x * 47 > 43^x * 43 + 4*43 := by
        rw [← add_mul]
        apply mul_lt_mul ih (by norm_num) (by norm_num) (by simp)
      linarith only [h1]

  have ineq2 {x:ℕ} (hx: x ≥ 1): 47^x-4 ≥ 43^x := by
    by_cases hx: x = 1
    · simp [hx]
    · replace hx: x ≥ 2 := by omega
      refine Nat.le_sub_of_add_le ?_
      apply le_of_lt (ineq1 hx)

  -- if (-1)^n mod eq -1, then n odd.
  have odd_of_neg1_pow {n:ℕ} (h: (-1)^n ≡ -1 [ZMOD 3]): Odd n := by
    rw [← Nat.not_even_iff_odd]
    rintro hn
    simp only [Int.reduceNeg, hn, Even.neg_pow, one_pow] at h
    contradiction

  -- if (-1)^n mod eq 1, then n even
  have even_of_neg1_pow {n:ℕ} (h: (-1)^n ≡ 1 [ZMOD 4]): Even n := by
    rw [← Nat.not_odd_iff_even]
    rintro hn
    simp only [Int.reduceNeg, hn, Odd.neg_one_pow] at h
    contradiction

  -- if n1 odd, (-3)^n1 + 4 mod 8 (-3)^n2, then n2 must be even.
  have even_of_mod8 {n1 n2: ℕ} (hn1: Odd n1) (h: -3^n1 + 4 ≡ (-3)^n2 [ZMOD 8]):
    Even n2 := by
    rw [← Nat.not_odd_iff_even]
    rintro hn2
    rw [odd_iff_exists_bit1] at hn1 hn2
    rcases hn1 with ⟨n1, rfl⟩
    rcases hn2 with ⟨n2, rfl⟩
    have h1: -3^(2*n1+1) ≡ 1^n1 * -3 [ZMOD 8] := by
      have h1: -3^(2*n1+1) = 9^n1 * -3 := by
        rw [pow_succ, pow_mul]
        ring
      have h2: 9^n1 ≡ 1^n1 [ZMOD 8] := by
        exact Int.ModEq.pow n1 rfl
      rw [h1]
      apply Int.ModEq.mul h2 rfl
    replace h1: - 3^(2*n1+1) + 4 ≡ 1 [ZMOD 8] := by
      have: 1 = -3 + 4 := by norm_num
      rw [this]
      apply Int.ModEq.add ?_ rfl
      apply h1.trans ?_
      simp
    have h2: (-3)^(2*n2+1) ≡ 9^n2 * -3 [ZMOD 8] := by
      rw [pow_succ, pow_mul]
      apply Int.ModEq.mul (by simp) rfl
    replace h2: (-3)^(2*n2+1) ≡ 1 * -3 [ZMOD 8] := by
      have: 9^n2 ≡ 1^n2 [ZMOD 8] := Int.ModEq.pow n2 rfl
      apply h2.trans ?_
      apply Int.ModEq.mul ?_ rfl
      apply this.trans (by simp)
    have: 1 ≡ -3 [ZMOD 8] := by
      rw [one_mul] at h2
      apply h1.symm.trans ?_
      apply h.trans h2
    clear * - this
    contradiction

  constructor
  · rintro ⟨anz, bnz, cnz, heq⟩
    -- try modulo 3,4,8, we find a is odd and b,c are even.

    have ha: Odd a := by
      -- modulo 3.
      have h1: 2021^a + 4 ≡ 0 [ZMOD 3] := by
        zify at heq
        rw [heq]
        refine Int.modEq_zero_iff_dvd.mpr ?_
        apply Dvd.dvd.mul_right (dvd_pow_self 3 bnz)
      -- 2021 mod 3 is -1, 4 mod 3 is 1, so (-1)^a + 1 = 0, a is odd.
      have h2: 2021^a ≡ -1 [ZMOD 3] := Int.ModEq.add_right_cancel' 4 h1
      have h3: (-1)^a ≡ -1 [ZMOD 3] := by
        apply Int.ModEq.trans ?_ h2
        exact Int.ModEq.pow a rfl
      apply odd_of_neg1_pow h3

    have hb: Even b := by
      -- modulo 4
      have h1: 2021^a + 4 ≡ 1 [MOD 4] := by
        rw [← add_zero 1]
        apply Nat.ModEq.add ?_ ?_
        · rw [← one_pow a]
          exact Nat.ModEq.pow a rfl
        · rfl
      have h2: 3^b * 5^c ≡ (-1)^b [ZMOD 4] := by
        have: (-1)^b = (-1)^b * 1^c := by simp
        rw [this]
        apply Int.ModEq.mul ?_ ?_
        · exact Int.ModEq.pow b rfl
        · exact Int.ModEq.pow c rfl
      have h3: (-1)^b ≡ 1 [ZMOD 4] := by
        rw [← Int.natCast_modEq_iff, heq] at h1
        push_cast at h1
        exact h2.symm.trans h1
      apply even_of_neg1_pow h3

    have hc: Even c := by
      -- modulo 8.
      have h1: 2021^a + 4 ≡ - 3^a + 4 [ZMOD 8] := by
        apply Int.ModEq.add ?_ rfl
        have: -3^a = (-3)^a := (Odd.neg_pow ha 3).symm
        rw [this]
        exact Int.ModEq.pow a rfl
      have h2: 3^b * 5^c ≡ (-3)^(b+c) [ZMOD 8] := by
        rw [pow_add]
        apply Int.ModEq.mul ?_ ?_
        · rw [Even.neg_pow hb 3]
        · exact Int.ModEq.pow c rfl
      have h3: -3^a + 4 ≡ (-3)^(b+c) [ZMOD 8] := by
        zify at heq
        rw [heq] at h1
        apply h1.symm.trans h2
      have: Even (b+c) := by
        apply even_of_mod8 ha h3
      rw [Nat.even_add] at this
      exact this.mp hb

    -- thus we show b,c are even.
    rcases (even_iff_exists_two_mul.mp hb) with ⟨b,rfl⟩
    rcases (even_iff_exists_two_mul.mp hc) with ⟨c,rfl⟩
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at bnz cnz

    -- notice that 2021 = 43 x 47.
    -- move 4 to the other side, factorization
    replace heq: 43^a * 47^a = (3^b*5^c+2)*(3^b*5^c-2) := by
      replace heq := Nat.eq_sub_of_add_eq heq
      have h1: 2021 = 43 * 47 := by norm_num
      have h2: 4 = 2^2 := by norm_num
      have h3: 3^(2*b) * 5^(2*c) = (3^b * 5^c)^2 := by ring
      rwa [h1, h2, h3, Nat.sq_sub_sq, Nat.mul_pow] at heq

    have h1: 3 ≤ 3^b * 5^c := by
      apply le_trans (Nat.le_self_pow bnz 3) ?_
      apply Nat.le_mul_of_pos_right _ (by simp)

    -- 3^b5^c + 2 and 3^b5^c - 2 are coprime
    have co: Nat.Coprime (3^b*5^c+2) (3^b*5^c-2) := by
      apply co_odd_add2 ?_ h1
      refine Nat.odd_mul.mpr ⟨?_, ?_⟩
      <;> apply Odd.pow (Nat.odd_iff.mpr rfl)

    -- then 47^a divide one of them, since 47 is prime.
    -- in fact, 47^a must divide the smaller one.
    have hdvd: 47^a ∣ 3^b*5^c + 2 := by
      have h2: 47^a ∣ (3^b*5^c+2) * (3^b*5^c-2) := by
        rw [← heq]
        apply Nat.dvd_mul_left
      have h3: IsPrimePow (47^a) := by
        refine IsPrimePow.pow ?_ anz
        exact Nat.Prime.isPrimePow (by norm_num)
      rw [Nat.Coprime.isPrimePow_dvd_mul co h3] at h2
      rcases h2 with h2 | h2
      · exact h2
      · replace h2: 47^a ≤ 3^b*5^c-2 := by
          apply Nat.le_of_dvd ?_ h2
          exact Nat.zero_lt_sub_of_lt h1
        replace h3: 43^a < 3^b * 5^c + 2 := by
          have: 43^a < 47^a := Nat.pow_lt_pow_left (by norm_num) anz
          apply lt_trans this (lt_of_le_of_lt h2 ?_)
          clear * -
          omega
        have: 43^a * 47^a < (3^b*5^c+2) * (3^b * 5^c - 2) := by
          exact Nat.mul_lt_mul_of_lt_of_le' h3 h2 (by simp)
        simp [heq] at this

    have h2: 3^b * 5^c - 2 = (3^b * 5^c + 2) - 4 := by
      clear * - h1
      omega

    -- clearly, we have 47^a = 3^b 5^c + 2, 43^a = 3^b 5^c - 2, moreover, a = 1.
    rcases hdvd with ⟨k, hk⟩
    have knz: k ≠ 0 := by
      rintro rfl
      simp at hk
    replace heq: 43^a = k*(47^a * k - 4) := by
      rw [mul_comm (43^a) _, h2, hk, mul_assoc] at heq
      simp only [mul_eq_mul_left_iff, pow_eq_zero_iff',
      OfNat.ofNat_ne_zero, ne_eq, false_and, or_false] at heq
      exact heq
    have keq1: k = 1 := by
      have hk1: k ≥ 1 := Nat.one_le_iff_ne_zero.mpr knz
      have hh1: 47^a*k ≥ 47^a := Nat.le_mul_of_pos_right _ hk1
      have hh2: 47^a - 4 ≥ 43^a := by
        apply ineq2 (Nat.one_le_iff_ne_zero.mpr anz)
      have hh3: 43^a = k * 43^a := by
        apply le_antisymm
        · exact Nat.le_mul_of_pos_left _ hk1
        · nth_rw 2 [heq]
          apply mul_le_mul_left'
          apply le_trans hh2 ?_
          exact Nat.sub_le_sub_right hh1 4
      simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
      not_false_eq_true, right_eq_mul₀] at hh3
      exact hh3
    have aeq1: a = 1 := by
      simp only [keq1, mul_one, one_mul] at heq
      replace heq: 47^a = 43^a + 4 := by
        rw [heq]
        have: 4 ≤ 47^a := by
          have: 47 ≤ 47^a := Nat.le_self_pow anz _
          apply le_trans (by norm_num) this
        simp [this]
      by_contra!
      replace: a ≥ 2 := by omega
      replace := ineq1 this
      simp [heq] at this

    -- then we can solve b=2, c=1 from 3^b 5^c = 45
    simp only [aeq1, pow_one, keq1, mul_one, Nat.reduceEqDiff] at hk
    replace hk := solve_eq1 hk
    simp [aeq1, hk]

  · --verification
    simp only [Prod.mk.injEq]
    rintro ⟨rfl,rfl,rfl⟩
    norm_num