import Mathlib

/- What is the smallest integer $x$ larger than 1 such that $x^{2}$ ends in the same three digits as $x$ does?-/
theorem number_theory_611337 {s : Set ℕ} (hs : s = {x : ℕ | 1 < x ∧ 1000 ∣ x ^ 2 - x}) :
    IsLeast s 376 := by
  -- It's clear that `n` and `n+1` are coprime.
  have hco_succ (n : ℕ) : n.Coprime (n + 1) := by
    rw [← Nat.coprime_self_sub_left (by omega)]
    simp
  -- It's clear that if `a` and `b` are coprime, then there does not exists `2≤d` such that
  -- `d` divdes `a` and `b`.
  have false_of_coprime_of_dvd_of_ge {a b d : ℕ} (hco : a.Coprime b) (hdvd : d ∣ a ∧ d ∣ b)
      (hge : 2 ≤ d) : False := by
    suffices d ∣ 1 by have := Nat.le_of_dvd (by norm_num) this; omega
    calc
      _ ∣ a.gcd b := Nat.dvd_gcd hdvd.1 hdvd.2
      _ = 1 := by rwa [Nat.coprime_iff_gcd_eq_one] at hco
  -- If `a` and `b` are coprime, `p` is prime, `p^k` divides `ab`, then
  -- either `p^k` divides `a` or `p^k` divides `b`.
  have dvd_of_coprime_of_prime_pow_dvd {p k a b : ℕ} (hco : a.Coprime b) (hp : p.Prime)
      (hdvd : p ^ k ∣ a * b) : p ^ k ∣ a ∨ p ^ k ∣ b := by
    have : Fact p.Prime := ⟨hp⟩
    rcases eq_or_ne k 0 with hk | hk
    . simp [hk, pow_zero]
    have : p ∣ a * b := Nat.dvd_trans (by
      rw [show k = k - 1 + 1 by omega, pow_succ]
      exact Nat.dvd_mul_left p _) hdvd
    rw [Nat.Prime.dvd_mul hp] at this
    rcases eq_or_ne (a * b) 0 with hab | hab
    . rw [mul_eq_zero] at hab
      rcases hab with ha | hb
      . left; norm_num [ha]
      . right; norm_num [hb]
    have hanz : a ≠ 0 := fun h => by norm_num [h] at hab
    have hbnz : b ≠ 0 := fun h => by norm_num [h] at hab
    rcases this with ha | hb
    . have hb : ¬p ∣ b := by
        intro h
        apply false_of_coprime_of_dvd_of_ge
        . exact hco
        . exact ⟨ha, h⟩
        . exact Nat.Prime.two_le hp
      rw [padicValNat_dvd_iff_le hab, padicValNat.mul hanz hbnz,
        padicValNat.eq_zero_of_not_dvd hb, add_zero, ← padicValNat_dvd_iff_le hanz] at hdvd
      left; exact hdvd
    . have ha : ¬p ∣ a := by
        intro h
        apply false_of_coprime_of_dvd_of_ge
        . exact hco
        . exact ⟨h, hb⟩
        . exact Nat.Prime.two_le hp
      rw [padicValNat_dvd_iff_le hab, padicValNat.mul hanz hbnz,
        padicValNat.eq_zero_of_not_dvd ha, zero_add, ← padicValNat_dvd_iff_le hbnz] at hdvd
      right; exact hdvd
  constructor
  . -- Verify that `376` satisfies requirement.
    norm_num [hs]
  . -- Show that `376` is the smallest.
    intro x hxmem
    -- Assume that there exists `x` less than `376` satisfies requirement.
    by_contra! hxlt
    rw [hs] at hxmem
    rcases hxmem with ⟨hxpos, hxdvd⟩
    -- By assumption, `1000` divides `x(x-1)`.
    replace hxdvd : 1000 ∣ x * (x - 1) := by
      convert hxdvd using 1
      zify
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by rw [pow_two]; exact Nat.le_mul_self x)]
      push_cast
      ring
    -- Notice that `x-1` and `x` are coprime.
    have xco_succ : (x - 1).Coprime x := by convert hco_succ (x - 1); omega
    -- Since `x-1` and `x` are coprime, `2^3` cannot divide both `x` and `x-1`.
    have not_two_pow_dvd_and : ¬(2 ^ 3 ∣ x ∧ 2 ^ 3 ∣ x - 1) := by
      rw [and_comm]
      intro h
      apply false_of_coprime_of_dvd_of_ge
      . exact xco_succ
      . exact h
      . norm_num
    -- Using lemma `dvd_of_coprime_of_prime_pow_dvd`.
    -- We can deduce that either `2^3` divides `x` or `2^3` divides `x-1`.
    have two_pow_dvd_or : 2 ^ 3 ∣ x ∨ 2 ^ 3 ∣ x - 1 := by
      rw [or_comm]
      apply dvd_of_coprime_of_prime_pow_dvd
      . exact xco_succ
      . exact Nat.prime_two
      . rw [mul_comm]
        exact Nat.dvd_trans (by norm_num) hxdvd
    -- Since `x-1` and `x` are coprime, `5^3` cannot divide both `x` and `x-1`.
    have not_five_pow_dvd_and : ¬(5 ^ 3 ∣ x ∧ 5 ^ 3 ∣ x - 1) := by
      rw [and_comm]
      intro h
      apply false_of_coprime_of_dvd_of_ge
      . exact xco_succ
      . exact h
      . norm_num
    -- Using lemma `dvd_of_coprime_of_prime_pow_dvd`.
    -- We can deduce that either `5^3` divides `x` or `5^3` divides `x-1`.
    have two_five_dvd_or : 5 ^ 3 ∣ x ∨ 5 ^ 3 ∣ x - 1 := by
      rw [or_comm]
      apply dvd_of_coprime_of_prime_pow_dvd
      . exact xco_succ
      . norm_num
      . rw [mul_comm]
        exact Nat.dvd_trans (by norm_num) hxdvd
    rw [not_and_or] at not_two_pow_dvd_and not_five_pow_dvd_and
    -- We split into two cases.
    rcases not_five_pow_dvd_and with h | h
    . -- If `5^3` does not divides `x`, then we must have `5^3` divides `x-1`.
      have ⟨k, hk⟩ := two_five_dvd_or.resolve_left h
      have : 0 < k := by omega
      have : k < 3 := by omega
      replace hk : x = 5 ^ 3 * k + 1 := by omega
      -- There are only two positive integers that satisfies:
      -- (1)`x<376`. (2)`5^3` divides `x-1`.
      obtain rfl | rfl : k = 1 ∨ k = 2 := by interval_cases k <;> norm_num
      -- Both of them do not satisfy `two_pow_dvd_or`.
      all_goals norm_num [hk] at two_pow_dvd_or
    . -- If `5^3` does not divides `x-1`, then we must have `5^3` divides `x`.
      have ⟨k, hk⟩ := two_five_dvd_or.resolve_right h
      have : 0 < k := by omega
      have : k < 3 := by omega
      -- There are only two positive integers that satisfies:
      -- (1)`x<376`. (2)`5^3` divides `x`.
      obtain rfl | rfl : k = 1 ∨ k = 2 := by interval_cases k <;> norm_num
      -- Both of them do not satisfy `two_pow_dvd_or`.
      all_goals norm_num [hk] at two_pow_dvd_or
