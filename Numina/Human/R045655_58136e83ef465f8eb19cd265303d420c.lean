import Mathlib

open Nat

/- ## Task A-1.7.

Determine all natural numbers $n$ for which among the numbers $n, 4^{n}+1$, and $n^{2}+2$ at least two are prime numbers. -/
theorem number_theory_241242 :
    {n : ℕ | 0 < n ∧ ((n.Prime ∧ (4^n + 1).Prime) ∨
    (n.Prime ∧ (n^2 + 2).Prime) ∨
    ((4^n + 1).Prime ∧ (n^2 + 2).Prime))} = {1, 2, 3} := by
  ext x
  simp
  constructor
  -- We check 1, 2, 3 are in the set.
  swap
  {
    rintro (rfl | rfl | rfl)
    all_goals native_decide
  }
  -- We have the important lemma.
  -- If x is odd and 4^x + 1 is prime, then x = 1.
  have lem (x : ℕ) (hxodd : Odd x) (hx : (4 ^ x + 1).Prime) : x = 1 := by
    -- 4 + 1 ∣ 4^x + 1^x
    have h : 5 ∣ 4 ^ x + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 4 1 hxodd
    -- So the only possibility is x = 1.
    rw [prime_dvd_prime_iff_eq (by norm_num) hx] at h
    replace h : 4 ^ x = 4 ^ 1 := by omega
    exact Nat.pow_right_injective (by simp) h
  -- We discuss the three cases.
  rintro ⟨h₀, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)⟩
  . -- x and 4^x + 1 are prime.
    -- x must be even by the important lemma.
    have h₃ : Even x := by
      by_contra! h₃
      simp at h₃
      norm_num [lem x h₃ h₂] at h₁
    -- So x = 2.
    obtain rfl : x = 2 := (Prime.even_iff h₁).mp h₃
    simp
  . -- x and n^2 + 2 are prime.
    have h₃ : 2 ≤ x := Prime.two_le h₁
    -- We check x mod 3.
    mod_cases x % 3
    . -- If x ≡ 0 (mod 3), then x = 3
      simp [modEq_zero_iff_dvd] at H
      rw [prime_dvd_prime_iff_eq (by norm_num) h₁] at H
      simp [← H]
    -- If x ≡ 1 or 2 (mod 3), then x^2 + 2 ≡ 0 (mod 3).
    -- So 3 ∣ x^2 + 2, contradicting the primality of x^2 + 2.
    all_goals
      simp [ModEq] at H
      have h₄ : (x ^ 2 + 2) % 3 = 0 := by
        rw [add_mod, pow_mod, H]
      apply dvd_of_mod_eq_zero at h₄
      rw [prime_dvd_prime_iff_eq (by norm_num) h₂] at h₄
      nlinarith
  . -- 4^x + 1 and n^2 + 2 are prime.
    -- Check the parity of x.
    obtain h₄ | h₄ := even_or_odd x
    . -- If x is even, then x ^ 2 + 2 is even.
      -- So x ^ 2 + 2 is not prime.
      have h₅ : Even (x ^ 2 + 2) := Even.add ((even_pow' (by simp)).mpr h₄) (by simp)
      replace h₅ : x ^ 2 + 2 = 2 := (Prime.even_iff h₂).mp h₅
      nlinarith
    . -- If x is odd, then x = 1 by the important lemma.
      simp [lem x h₄ h₁]
