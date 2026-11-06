import Mathlib

open Finset

/- A perfect power is an integer n that can be represented as a^k for some positive integers a ≥ 1 and k ≥ 2. -/
def IsPerfectPower (x : ℕ) : Prop := ∃ a ≥ 1, ∃ k ≥ 2, a ^ k = x

/- We show that a number is a perfect power if and only if it is not 0 and the gcd of its prime factors and its factorization is not 1. -/
lemma IsPerfectPowerIff (x : ℕ) :
    IsPerfectPower x ↔ (x ≠ 0 ∧ gcd x.primeFactors x.factorization ≠ 1) := by
  -- We first discuss the case where x = 0
  by_cases hx : x = 0
  . simp [hx, IsPerfectPower]
    intro a ha k hk ha'
    simp [ha'] at ha
  -- We now discuss the case where x ≠ 0
  constructor
  . -- If x = a ^ k is a perfect power
    rintro ⟨a, ha, k, hk, rfl⟩
    simp [hx]
    intro H
    -- Then for any prime factor p of x, we have k ∣ v_p(x)
    simp [show (fun x => k) * ⇑a.factorization = fun x => k * a.factorization x by ext x; simp,
      Nat.primeFactors_pow a (show k ≠ 0 by omega),
      Finset.gcd_mul_left,
      show k ≠ 1 by omega] at H
  . -- If x is not 0 and the gcd of its prime factors and its factorization is not 1
    simp [hx]
    intro H
    -- Then it has a divisor k ≥ 2
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k ≥ 2, k ∣ x.primeFactors.gcd x.factorization := by
      obtain hk | hk : x.primeFactors.gcd x.factorization = 0 ∨ x.primeFactors.gcd x.factorization ≥ 2 := by omega
      . simp [hk]
        exact ⟨2, by simp⟩
      . exact ⟨x.primeFactors.gcd x.factorization, hk, by simp⟩
    -- We have k ∣ v_p(x) for all prime factors p of x
    simp [Finset.dvd_gcd_iff, hx] at hk₂
    -- Let a be the product of p ^ (v_p(x) / k) for all prime factors p of x
    let a := ∏ p ∈ x.primeFactors, p ^ (x.factorization p / k)
    have hx₁ := Nat.factorization_prod_pow_eq_self hx
    simp [Finsupp.prod] at hx₁
    -- We have a ≠ 0 and a ^ k = x
    have ha₁ : a ≠ 0 := by
      simp [a, prod_eq_zero_iff, hx, show k ≠ 0 by omega]
      rintro p hp₁ hp₂ rfl
      norm_num at hp₁
    have ha₂ : a ^ k = x := by
      simp [a, ← prod_pow, ← pow_mul]
      conv_rhs =>
        rw [← hx₁]
      apply prod_congr rfl
      intro p hp
      simp at hp
      congr
      exact Nat.div_mul_cancel (hk₂ p hp.1 hp.2.1)
    exact ⟨a, by omega, k, hk₁, ha₂⟩

instance (x : ℕ) : Decidable (IsPerfectPower x) := decidable_of_iff' _ (IsPerfectPowerIff x)

/- A perfect power is an integer $n$ that can be represented as $a^{k}$ for some positive integers $a \geq 1$ and $k \geq 2$. Find the sum of all prime numbers $0<p<50$ such that $p$ is 1 less than a perfect power. -/
theorem number_theory_610350 :
    ∑ x ∈ {x ∈ Ioo 0 50 | x.Prime ∧ IsPerfectPower (x + 1)}, x = 41 := by
  -- The set is {3, 7, 31} by computation
  -- So the answer is 3 + 7 + 31 = 41
  native_decide
