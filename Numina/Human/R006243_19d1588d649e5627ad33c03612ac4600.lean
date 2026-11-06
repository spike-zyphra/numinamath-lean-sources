import Mathlib

/- Let $k$ be a non-negative integer. Given $a = 2^6 \times 3^3 \times 6^k$, determine the number of positive divisors of $a$. Show that this number is equal to $(k+7)(k+4)$. -/
theorem number_theory_635102 (k : ℕ) :
    (2 ^ 6 * 3 ^ 3 * 6 ^ k).divisors.card = (k + 7) * (k + 4) := by
  -- We first show that a = 2 ^ (k + 6) * 3 ^ (k + 3).
  have h₁ : 2 ^ 6 * 3 ^ 3 * 6 ^ k = 2 ^ (k + 6) * 3 ^ (k + 3) := by
    rw [pow_add, pow_add, show 6 ^ k = (2 * 3) ^ k by rfl, mul_pow]
    group
  rw [h₁]
  -- We show that the prime factors of a are 2 and 3.
  have h₂ : (2 ^ (k + 6) * 3 ^ (k + 3)).primeFactors = ⟨{2, 3}, by simp⟩ := by
    -- We need to show biimplication.
    ext p
    simp only [Nat.mem_primeFactors, ne_eq, mul_eq_zero, AddLeftCancelMonoid.add_eq_zero,
      OfNat.ofNat_ne_zero, and_false, not_false_eq_true, pow_eq_zero_iff, or_self, and_true,
      Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert, Finset.mem_insert,
      Finset.mem_mk, Multiset.mem_singleton]
    constructor
    -- If p is a prime factor of a:
    . rintro ⟨hp, h⟩
      -- Then p either divides 2 ^ (k + 6) or 3 ^ (k + 3).
      rw [Nat.Prime.dvd_mul hp] at h
      rcases h with h | h
      . -- If p divides 2 ^ (k + 6), then p divides 2.
        left
        apply Nat.Prime.dvd_of_dvd_pow hp at h
        -- So p = 2.
        rwa [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two] at h
      . -- If p divides 3 ^ (k + 3), then p divides 3.
        right
        apply Nat.Prime.dvd_of_dvd_pow hp at h
        -- So p = 3.
        rwa [Nat.prime_dvd_prime_iff_eq hp Nat.prime_three] at h
    -- If p = 2 or p = 3:
    . rintro (rfl | rfl)
      . -- If p = 2, then p divides 2 ^ (k + 6).
        norm_num
        suffices 2 ∣ 2 ^ (k + 6) from Dvd.dvd.mul_right this _
        exact Dvd.intro_left (2 ^ (k + 5)) rfl
      . -- If p = 3, then p divides 3 ^ (k + 3).
        norm_num
        suffices 3 ∣ 3 ^ (k + 3) from Dvd.dvd.mul_left this _
        exact Dvd.intro_left (3 ^ (k + 2)) rfl
  -- We use the lemma `Nat.card_divisors` to count the number of divisors of a.
  -- The number of divisors of p₁ ^ k₁ * p₂ ^ k₂ * ... * pₙ ^ kₙ is (k₁ + 1) * (k₂ + 1) * ... * (kₙ + 1).
  rw [Nat.card_divisors (by positivity), h₂]
  -- Simplify the expression.
  simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, OfNat.ofNat_ne_zero, and_false, not_false_eq_true,
    pow_eq_zero_iff, Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add,
    Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_add, Pi.natCast_def, Nat.cast_id, Nat.cast_ofNat,
    Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply, Finset.mem_mk, Multiset.mem_singleton,
    Nat.reduceEqDiff, Finset.prod_insert, Finset.prod_mk, Multiset.map_singleton,
    Multiset.prod_singleton]
  -- Simplify with Nat.factorization 2 2 = 1, Nat.factorization 3 2 = 0, Nat.factorization 2 3 = 0, Nat.factorization 3 3 = 1.
  rw [show Nat.factorization 2 2 = 1 by native_decide,
      show Nat.factorization 3 2 = 0 by native_decide,
      show Nat.factorization 2 3 = 0 by native_decide,
      show Nat.factorization 3 3 = 1 by native_decide]
  ring