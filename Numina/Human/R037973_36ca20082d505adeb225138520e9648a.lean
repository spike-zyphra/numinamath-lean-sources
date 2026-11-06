import Mathlib

/- Determine the largest positive integer $n$ that divides $p^{6}-1$ for all primes $p>7$. -/
theorem number_theory_605331 : IsGreatest {n | 0 < n ∧ ∀ p, Nat.Prime p → p > 7 → n ∣ (p^6 - 1)} 504 := by
  constructor
  -- First, we show that 504 ∣ p^6 - 1 for all primes p > 7.
  . simp
    intro p hp hp'
    -- Cast the expression to ℤ
    zify
    simp [show 0 < p ^ 6 by positivity]
    -- As 504 = lcm {7, 8, 9}, we have that 504 ∣ p^6 - 1 if and only if 7, 8, 9 ∣ p^6 - 1.
    rw [show (504 : ℤ) = Multiset.lcm {7, 8, 9} by rfl, Multiset.lcm_dvd]
    -- Now we show that 7, 8, 9 ∣ p^6 - 1.
    simp
    refine ⟨?_, ?_, ?_⟩
    . -- 7 ∣ p^6 - 1
      -- We cast the expression to ZMod 7
      rw [show (7 : ℤ) = (7 : ℕ) by rfl,
          ← ZMod.intCast_eq_intCast_iff_dvd_sub,
          show 6 = 7 - 1 by simp]
      simp
      symm
      -- From Fermat's Little Theorem, we have that p^6 = 1 in ZMod 7 as long as p is not 0 in ZMod 7.
      apply @ZMod.pow_card_sub_one_eq_one _ (by decide) _
      -- But p is a prime greater than 7, so it is not 0 in ZMod 7.
      simp [ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.prime_dvd_prime_iff_eq (show Nat.Prime 7 by decide) hp]
      exact Nat.ne_of_lt hp'
    . -- 8 ∣ p^6 - 1
      -- We know that p is odd, so is p ^ 3, and we can replace p with 2k + 1 for some k.
      replace hp' : Odd p := Nat.Prime.odd_of_ne_two hp (by omega)
      apply Odd.pow (n := 3) at hp'
      obtain ⟨k, h⟩ := hp'
      zify at h
      -- Now p ^ 6 - 1 = (2k + 1) ^ 2 - 1 = 4k (k + 1)
      rw [show (p ^ 6 : ℤ) = (p ^ 3) ^ 2 by ring, h]
      -- We do case analysis on the parity of k.
      obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ : Even k ∨ Odd k := Nat.even_or_odd k
      -- We can see that 4k (k + 1) is divisible by 8 in both cases.
      all_goals
        simp
        ring_nf
        omega
    . -- 9 ∣ p^6 - 1
      -- 6 = φ(9)
      -- So we can use Euler's Theorem.
      have h := Nat.ModEq.pow_totient (show p.Coprime 9 from ?_)
      -- We can see that p ^ 6 ≡ 1 (mod 9) as long as p is coprime to 9.
      symm at h
      simp [Nat.modEq_iff_dvd] at h
      rw [show Nat.totient 9 = 6 by decide] at h
      exact h
      {
        -- We show that p is coprime to 9.
        -- It is equivalent to p being coprime to 3.
        change p.Coprime (3 ^ 2)
        -- But p is a prime greater than 3, so it is coprime to 3.
        rw [Nat.coprime_pow_right_iff (by simp),
            Nat.coprime_primes hp (Nat.prime_three)]
        omega
      }
  . -- Now we show that 504 is the largest such integer.
    simp [upperBounds]
    -- Let n be an integer such that n ∣ p^6 - 1 for all primes p > 7.
    intro n hn h
    -- Set p = 11 and 13
    -- We get n ∣ 11 ^ 6 - 1 and n ∣ 13 ^ 6 - 1
    have h₁ := h 11 (by decide) (by simp)
    have h₂ := h 13 (by decide) (by simp)
    -- So n divides the gcd of 11 ^ 6 - 1 and 13 ^ 6 - 1, which is 504.
    have h₃ : n ∣ Nat.gcd (11 ^ 6 - 1) (13 ^ 6 - 1) := Nat.dvd_gcd h₁ h₂
    simp at h₃
    -- So n ≤ 504.
    exact Nat.le_of_dvd (show 0 < 504 by simp) h₃
