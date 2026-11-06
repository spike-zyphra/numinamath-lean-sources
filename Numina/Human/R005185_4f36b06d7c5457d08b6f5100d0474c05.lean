import Mathlib

/- Bepaal het product van alle positieve gehele getallen $n$ waarvoor $3(n!+1)$ deelbaar is door $2 n-5$. -/
theorem number_theory_606126 :
    ∏ᶠ n ∈ {n : ℕ | 0 < n ∧ (2 * n - 5 : ℤ) ∣ 3 * (Nat.factorial n + 1)}, n = 2016 := by
  -- Show that only such values of n are 1, 2, 3, 4, 6 and 14.
  suffices {n : ℕ | 0 < n ∧ (2 * n - 5 : ℤ) ∣ 3 * (Nat.factorial n + 1)} = {1, 2, 3, 4, 6, 14} by
    rw [this, finprod_mem_eq_toFinset_prod]
    simp
  ext n
  constructor
  simp
  . -- First show that 2n - 5 ∣ 3(n! + 1) implies n = 1, 2, 3, 4, 6 or 14.
    intro hn h₀
    by_cases h₁ : n ≤ 4
    . -- The case n ≤ 4 is straightforward.
      omega
    . -- It suffices to consider n > 4, and we shall first show that 2n - 5 is a prime.
      let m := (2 * n - 5 : ℤ).natAbs
      have hm₀ : m = (2 * n - 5 : ℤ) := by
        simp [m]
        omega
      -- Note that 9 ∤ m.
      have hm₁ : ¬9 ∣ m := by
        -- Assume on the contrary that 9 divides m.
        by_contra! hm₁
        -- Then 9 divides 2n - 5, which implies 9 ∣ 3(n! + 1), but n > 4, contradiction.
        have h₂ : 3 * 3 ∣ 3 * (Nat.factorial n + 1) := by
          zify at hm₁ ⊢
          rw [hm₀] at hm₁
          exact hm₁.trans h₀
        apply Nat.dvd_of_mul_dvd_mul_left (by positivity) at h₂
        rw [<-Nat.dvd_add_iff_right (by apply Nat.dvd_factorial; norm_num; omega)] at h₂
        norm_num at h₂
      -- Show that m is prime.
      have hm₂ : Nat.Prime m := by
        -- Assume on the contrary that m is not prime.
        by_contra! hm₂
        -- Show that m has a prime factor p > 3.
        have h₂ : ∃ p : ℕ, p > 3 ∧ Nat.Prime p ∧ p ∣ m := by
          by_cases hm₃ : 3 ∣ m
          . -- Suppose 3 ∣ m, then we consider m / 3, which is not divisible by 3.
            replace hm₁ : ¬3 ∣ m / 3 := by
              omega
            obtain ⟨p, hm₄, hm₅⟩ := Nat.exists_prime_and_dvd (show m / 3 ≠ 1 by omega)
            use p
            refine ⟨?_, hm₄, ?_⟩
            . -- Show that p ≠ 2.
              have h₂ : p ≠ 2 := by
                by_contra! h₂
                -- If p = 2, then 2 ∣ 2n - 5.
                zify at hm₅
                rw [h₂, hm₀] at hm₅
                omega
              -- Show that p ≠ 3, so p > 3.
              have h₃ : p ≠ 3 := by
                by_contra! h₃
                -- If p = 3, then 3 ∣ m / 3, contradiction.
                rw [h₃] at hm₅
                contradiction
              have h₄ := Nat.Prime.two_le hm₄
              omega
            . -- Show that p ∣ m.
              rw [<-Nat.mul_div_cancel' hm₃]
              calc
                p ∣ m / 3 := hm₅
                _ ∣ 3 * (m / 3) := by
                  apply dvd_mul_left
          . -- Suppose 3 ∤ m, we directly find a prime factor of m.
            obtain ⟨p, hm₄, hm₅⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
            use p
            refine ⟨?_, hm₄, hm₅⟩
            . -- Show that p ≠ 2.
              have h₂ : p ≠ 2 := by
                by_contra! h₂
                -- If p = 2, then 2 ∣ 2n - 5.
                zify at hm₅
                rw [h₂, hm₀] at hm₅
                omega
              -- Show that p ≠ 3, so p > 3.
              have h₃ : p ≠ 3 := by
                by_contra! h₃
                -- If p = 3, then 3 ∣ m, contradiction.
                rw [h₃] at hm₅
                contradiction
              have h₄ := Nat.Prime.two_le hm₄
              omega
        obtain ⟨p, hp₀, hp₁, hp₂⟩ := h₂
        -- Write m = pq for some q.
        rw [dvd_iff_exists_eq_mul_left] at hp₂
        obtain ⟨q, h₂⟩ := hp₂
        rw [<-hm₀] at h₀
        -- Note that p, q ≤ n.
        have h₃ : q ≤ n := by
          nlinarith
        have h₄ : p ≤ n := by
          have hq₀ : q ≠ 0 := by
            by_contra!
            -- If q = 0, then m = 0, which is absurd.
            simp [this] at h₂
            omega
          have hq₁ : q ≠ 1 := by
            by_contra!
            -- If q = 1, then p = m, which is not prime.
            rw [h₂, this, one_mul] at hm₂
            contradiction
          have hq₂ : q ≠ 2 := by
            by_contra!
            -- If q = 2, then 2 ∣ 2n - 5.
            simp [h₂, this] at h₀
            replace h₀ : 2 ∣ 3 * (Nat.factorial n + 1) := by
              zify
              calc
                2 ∣ (2 * p : ℤ) := by
                  omega
                _ ∣ 3 * (Nat.factorial n + 1) := h₀
            -- But 2 does not divide 3(n! + 1) for n > 4.
            apply Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) at h₀
            rw [<-Nat.dvd_add_iff_right (by apply Nat.dvd_factorial; norm_num; omega)] at h₀
            norm_num at h₀
          have hq₃ : q ≥ 3 := by
            omega
          nlinarith
        -- We derive a contradiction from m ∣ 3(n! + 1).
        by_cases h₅ : 3 ∣ q
        . -- If 3 ∣ q, then p has a divisor (clearly smaller than n) which divides n! + 1, a contradiction.
          simp [h₂] at h₀
          rw [dvd_iff_exists_eq_mul_right] at h₅
          obtain ⟨c, h₅⟩ := h₅
          zify at h₅
          rw [h₅, mul_assoc] at h₀
          rw [mul_dvd_mul_iff_left (by norm_num)] at h₀
          -- We have p ∣ n! + 1.
          replace h₀ : p ∣ Nat.factorial n + 1 := by
            zify
            calc
              _ ∣ (c * p : ℤ) := by
                apply dvd_mul_left
              _ ∣ Nat.factorial n + 1 := h₀
          rw [<-Nat.dvd_add_iff_right (by apply Nat.dvd_factorial (Nat.Prime.pos hp₁) (by omega))] at h₀
          simp at h₀
          norm_num [h₀] at hp₁
        . -- If 3 ∤ q, then q ∣ n! + 1, a contradiction.
          simp [h₂] at h₀
          replace h₀ : q ∣ 3 * (Nat.factorial n + 1) := by
            zify
            calc
              _ ∣ (q * p : ℤ) := by
                apply dvd_mul_right
              _ ∣ 3 * (Nat.factorial n + 1) := h₀
          -- We have q ∣ n! + 1.
          apply Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h₅).symm at h₀
          rw [<-Nat.dvd_add_iff_right (by apply Nat.dvd_factorial (by nlinarith) (by omega))] at h₀
          simp at h₀
          simp [h₂, h₀] at hm₂
          contradiction
      -- Copy the original condition (2n - 5) ∣ 3(n! + 1) for later use.
      have h := h₀
      -- Apply Wilson's theorem that (m - 1)! ≡ -1 (mod m).
      have h₂ := @ZMod.wilsons_lemma m (by rw [fact_iff]; exact hm₂)
      -- Eliminate the ZMod.
      symm at h₂
      rw [show ((m - 1).factorial : ZMod m) = ((m - 1).factorial : ℤ) by norm_cast, show (-1 : ZMod m) = (-1 : ℤ) by norm_cast, ZMod.intCast_eq_intCast_iff_dvd_sub] at h₂
      -- Simplify to get m ∣ (m - 1)! + 1.
      simp at h₂
      norm_cast at h₂
      -- Also get m ∣ n! + 1 from the original condition.
      rw [<-hm₀] at h₀
      norm_cast at h₀
      apply Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hm₂ Nat.prime_three).mpr (by omega)) at h₀
      -- Eliminate the case m = 5.
      have hm₃ : m ≠ 5 := by
        by_contra! hm₃
        replace hm₀ : n = 5 := by
          omega
        norm_num [hm₃, hm₀] at h₀
        absurd h₀
        decide
      -- We have m > 6.
      replace hm₃ : m > 6 := by
        omega
      -- We have n! * (n + 1) * ⋯ * (2n - 6) + 1 ≡ 0 (mod m).
      nth_rw 2 [show m = 2 * n - 5 by omega] at h₂
      rw [<-@Nat.factorial_mul_descFactorial _ (n - 6) (by omega), show 2 * n - 5 - 1 - (n - 6) = n by omega, Nat.descFactorial_eq_prod_range] at h₂
      zify at h₂
      rw [<-Int.modEq_zero_iff_dvd] at h₂
      -- We further have m ∣ Nat.factorial n * Nat.factorial (n - 6) + 1.
      replace h₂ : (m : ℤ) ∣ (-1) ^ (n - 6) * Nat.factorial n * Nat.factorial (n - 6) + 1 := by
        rw [<-Int.modEq_zero_iff_dvd]
        calc
          _ ≡ (Nat.factorial n * (-1) ^ (n - 6) * ∏ i ∈ Finset.range (n - 6), (i + 1) + 1 : ℤ) [ZMOD (m : ℤ)] := by
            rw [mul_comm _ (Nat.factorial n : ℤ)]
            congr
            rw [<-Finset.prod_range_add_one_eq_factorial]
          _ ≡ Nat.factorial n * ∏ i ∈ Finset.range (n - 6), (2 * n - 5 - 1 - i) + 1 [ZMOD (m : ℤ)] := by
            -- We basically use the fact that 2n - 5 - 1 - i = -(i + 1) (mod m) for i = 0, ..., n - 5.
            apply Int.ModEq.add_right
            rw [mul_assoc]
            apply Int.ModEq.mul_left
            push_cast
            rw [Finset.pow_eq_prod_const, <-Finset.prod_mul_distrib, <-ZMod.intCast_eq_intCast_iff]
            push_cast
            -- Show that ∏ x ∈ Finset.range (n - 6), (x + 1) = ∏ x ∈ Finset.range (n - 6), -(2 * n - 6 - x).
            rw [Finset.prod_congr (by rfl)]
            intro i hi
            simp at hi
            rw [show ((2 * n - 5 - 1 - i : ℕ) : ZMod m) = ((2 * n - 6 - i : ℤ) : ZMod m) by rw [show (2 * n - 6 - i : ℤ) = (2 * n - 5 - 1 - i : ℕ) by omega]; simp]
            rw [show -1 * (i + 1 : ZMod m) = ((-1 + -i : ℤ) : ZMod m) by simp]
            rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
            simp [hm₀]
            ring_nf
            rfl
          _ ≡ (0 : ℤ) [ZMOD (m : ℤ)] := by
            simp [h₂]
      -- Multiply on both sides of h₂ by n(n - 1)(n - 2)(n - 3)(n - 4)(n - 5) to get m ∣ (-1) ^ (n - 6) * n! * n! + n(n - 1)(n - 2)(n - 3)(n - 4)(n - 5).
      replace h₂ := dvd_mul_of_dvd_left h₂ (n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) : ℕ)
      rw [add_mul, mul_assoc, mul_comm (Nat.factorial (n - 6) : ℤ)] at h₂
      norm_cast at h₂
      repeat rw [mul_assoc] at h₂
      rw [show n - 6 = n - 5 - 1 by omega, show n - 5 = n - 4 - 1 by omega, show n - 4 = n - 3 - 1 by omega, show n - 3 = n - 2 - 1 by omega, show n - 2 = n - 1 - 1 by omega] at h₂
      iterate 6 rw [Nat.mul_factorial_pred (by omega)] at h₂
      rw [show Int.negSucc 0 ^ (n - 1 - 1 - 1 - 1 - 1 - 1) = (-1) ^ (n - 6) by simp; congrm (-1) ^ ?_; omega] at h₂
      -- Multiply on both sides of h₀ by (-1) ^ (n - 6) * (n! - 1) to get m ∣ (-1) ^ (n - 6) * n! * n! - (-1) ^ (n - 6)
      zify at h₀
      replace h₀ := dvd_mul_of_dvd_left h₀ ((-1) ^ (n - 6) * (Nat.factorial n - 1))
      rw [mul_comm, mul_assoc, mul_comm (Nat.factorial n - 1 : ℤ), <-sq_sub_sq, mul_sub, pow_two] at h₀
      -- Get m ∣ (-1) ^ (n - 6) * 64 + 2n(2n - 2)(2n - 4)(2n - 6)(2n - 8)(2n - 10) by 64 * (h₂ - h₀).
      have h₃ := dvd_sub h₂ h₀
      simp at h₃
      replace h₃ := dvd_mul_of_dvd_left h₃ 64
      rw [add_mul] at h₃
      repeat rw [Int.ofNat_sub (by omega)] at h₃
      simp at h₃
      rw [show n * ((n - 1 : ℤ) * ((n - 1 - 1 : ℤ) * ((n - 1 - 1 - 1 : ℤ) * ((n - 1 - 1 - 1 - 1 : ℤ) * (n - 1 - 1 - 1 - 1 - 1 : ℤ))))) * 64 = (2 * n : ℤ) * (2 * n - 2 : ℤ) * (2 * n - 4 : ℤ) * (2 * n - 6 : ℤ) * (2 * n - 8) * (2 * n - 10) by ring_nf, <-Int.modEq_zero_iff_dvd] at h₃
      -- We have m ∣ 5 ⬝ 3 ⬝ 1 ⬝ -1 ⬝ -3 ⬝ -5 + (-1) ^ (n - 6) * 64.
      replace h₃ : (m : ℤ) ∣ (-225 + (-1) ^ (n - 6) * 64 : ℤ) := by
        rw [<-Int.modEq_zero_iff_dvd]
        calc
          _ = (5 * 3 * 1 * (-1) * (-3) * (-5) + (-1) ^ (n - 6) * 64 : ℤ) := by
            ring_nf
          _ ≡ (2 * n) * (2 * n - 2) * (2 * n - 4) * (2 * n - 6) * (2 * n - 8) * (2 * n - 10) + (-1) ^ (n - 6) * 64 [ZMOD m] := by
            apply Int.ModEq.add_right
            iterate 5 apply Int.ModEq.mul
            all_goals
              rw [hm₀, Int.modEq_iff_dvd]
              try
                ring_nf
                rfl
          _ ≡ (0 : ℤ) [ZMOD m] := h₃
      by_cases h₄ : Odd n
      . -- Suppose n is odd, we have n = 11, but it does not satisfy the original condition.
        simp [Odd] at h₄
        norm_num [neg_one_pow_eq_pow_mod_two, show (n - 6) % 2 = 1 by omega] at h₃
        -- We have m ∣ 289 and m is a prime, hence m ∣ 17.
        rw [show (289 : ℤ) = 17 ^ 2 by norm_num] at h₃
        apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hm₂ at h₃
        simp at h₃
        -- Since m ∣ 17 and both m and 17 are primes, we have m = 17, and hence n = 11.
        rw [Nat.prime_dvd_prime_iff_eq hm₂ (by native_decide)] at h₃
        have h₅ : n = 11 := by
          omega
        -- Plugging m = 17 and n = 11 into the original condition, which gives a contradiction.
        norm_num [hm₀, h₅] at h
        absurd h
        decide
      . -- Suppose n is even, we have n = 14.
        simp [Even] at h₄
        norm_num [neg_one_pow_eq_pow_mod_two, show (n - 6) % 2 = 0 by omega] at h₃
        rw [show (161 : ℤ) = 7 * 23 by norm_num] at h₃
        -- We have m ∣ 161 = 7 * 23 and m is a prime, hence m = 7 or m = 23.
        norm_cast at h₃
        rw [Nat.Prime.dvd_mul hm₂] at h₃
        rcases h₃ with (h₃ | h₃)
        . -- Suppose m ∣ 7, then m = 7, n = 6, but we already assumed n > 6.
          rw [Nat.prime_dvd_prime_iff_eq hm₂ (by native_decide)] at h₃
          omega
        . -- Suppose m ∣ 23, then n = 14, which is one of our solutions.
          rw [Nat.prime_dvd_prime_iff_eq hm₂ (by native_decide)] at h₃
          omega
  . -- Show that 1, 2, 3, 4, 6, 14 are indeed solutions.
    simp
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      norm_num
      try decide
