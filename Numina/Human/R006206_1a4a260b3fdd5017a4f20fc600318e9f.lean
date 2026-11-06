import Mathlib

/- Let $p$ be a prime number such that $M_p = 2^p - 1$ is also a prime number. (A prime number of the form $2^p-1$ is often called a Mersenne prime.) Let $N = 2^{p-1} M_p$. Show that $N$ is a perfect number. A natural number is said to be perfect if the sum of all its proper divisors (that is, divisors different from the number itself) is equal to the number itself. For example, 6 and 28 are perfect, since $6=1+2+3$ and $28=1+2+4+7+14$. -/
theorem number_theory_634641 (p : ℕ) (hp : Nat.Prime p) (h : Nat.Prime (2 ^ p - 1)) :
    Nat.Perfect (2 ^ (p - 1) * (2 ^ p - 1)) := by
  -- Some basic facts.
  have h₁ : 2 ≠ 2 ^ p - 1 := by
    cases p
    . simp
    . omega
  have h₂ : 2 ^ p - 1 ≠ 0 := Nat.Prime.ne_zero h
  have h₃ : 0 < 2 ^ (p - 1) * (2 ^ p - 1) := by positivity
  -- We show that the prime factors of $N$ are $2$ and $2^p - 1$.
  have h₄ : (2 ^ (p - 1) * (2 ^ p - 1)).primeFactors = ⟨{2, 2 ^ p - 1}, by simp [h₁]⟩ := by
    -- We need to show biimplication.
    ext q
    simp [h₂]
    constructor
    . -- If $q$ is a prime factor of $N$, then $q$ is either $2$ or $2^p - 1$.
      rintro ⟨hq, h₁⟩
      rw [Nat.Prime.dvd_mul hq] at h₁
      -- Since $q$ is prime, it must either divide $2^{p-1}$ or $2^p - 1$.
      rcases h₁ with h₁ | h₁
      . -- If $q$ divides $2^{p-1}$, then $q = 2$.
        left
        apply Nat.Prime.dvd_of_dvd_pow hq at h₁
        rwa [Nat.prime_dvd_prime_iff_eq hq Nat.prime_two] at h₁
      . -- If $q$ divides $2^p - 1$, then $q = 2^p - 1$.
        right
        exact (Nat.prime_dvd_prime_iff_eq hq h).mp h₁
    . -- We show both $2$ and $2^p - 1$ are prime factors of $N$.
      rintro (rfl | rfl)
      . simp only [Nat.prime_two, true_and]
        suffices 2 ∣ 2 ^ (p - 1) from Dvd.dvd.mul_right this (2 ^ p - 1)
        refine dvd_pow_self 2 (by simp [Nat.sub_ne_zero_iff_lt, Nat.Prime.one_lt hp])
      . simp only [h, dvd_mul_left, and_self]
  -- We need to show that the sum of the factors of $N$ is equal to $2N$.
  -- We use the fact that the sum of the factors of $N$ is equal to (1 + p₁ + p₁ ^ 2 + ... + p₁ ^ (k₁ - 1)) * (1 + p₂ + p₂ ^ 2 + ... + p₂ ^ (k₂ - 1)) * ... * (1 + pₙ + pₙ ^ 2 + ... + pₙ ^ (kₙ - 1))
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul h₃, Nat.sum_divisors h₃.ne', h₄]
  simp [Finset.prod]
  -- We compute the factorization of $N$.
  have H₁ : (2 ^ (p - 1) * (2 ^ p - 1)).factorization 2 = p - 1 := by
    -- $v_2(N) = v_2(2^{p-1}) + v_2(2^p - 1) = p - 1 + 0 = p - 1$.
    rw [Nat.factorization_def _ Nat.prime_two, padicValNat.mul (by positivity) (by positivity), padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd, Nat.add_zero]
    . refine Odd.not_two_dvd_nat ?_
      exact Nat.Prime.odd_of_ne_two h (Ne.symm h₁)
  have H₂ : (2 ^ (p - 1) * (2 ^ p - 1)).factorization (2 ^ p - 1) = 1 := by
    have inst : Fact (2 ^ p - 1).Prime := ⟨h⟩
    -- $v_{2^p - 1}(N) = v_{2^p - 1}(2^{p-1}) + v_{2^p - 1}(2^p - 1) = 0 + 1 = 1$.
    rw [Nat.factorization_def _ h, padicValNat.mul (by positivity) (by positivity), padicValNat.pow _ (by simp), padicValNat.eq_zero_of_not_dvd (by simpa [Nat.prime_dvd_prime_iff_eq h Nat.prime_two] using Ne.symm h₁), padicValNat.self (Nat.Prime.one_lt h), Nat.mul_zero]
  rw [H₁, H₂]
  -- We use the formula for the sum of a geometric series.
  -- After simplifying, we get the desired result.
  simp [Nat.Prime.one_le hp, Nat.one_le_two_pow, Nat.geomSum_eq, ← mul_assoc, ← pow_succ']
  exact Nat.mul_comm _ _