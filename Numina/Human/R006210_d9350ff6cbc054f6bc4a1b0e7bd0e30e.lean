import Mathlib

/- Let $k$ be a natural number such that $k \ge 1$. Let $N = 2^{k-1}(2^k-1)$. If $2^k-1$ is a prime number, show that the sum of all proper divisors of $N$ is equal to $N$. -/
theorem number_theory_634666 (k : ℕ) (hk : 1 ≤ k) (h : Nat.Prime (2 ^ k - 1)) :
    ∑ i ∈ (2 ^ (k - 1) * (2 ^ k - 1)).properDivisors, i = 2 ^ (k - 1) * (2 ^ k - 1) := by
  -- Some basic facts.
  have h₁ : 2 ≠ 2 ^ k - 1 := by
    cases k
    . simp
    . omega
  have h₂ : 2 ^ k - 1 ≠ 0 := Nat.Prime.ne_zero h
  have h₃ : 0 < 2 ^ (k - 1) * (2 ^ k - 1) := by positivity
  have hk' : 1 < k := by
    by_contra! hk
    interval_cases k
    norm_num at h
  -- We show that the prime factors of $N$ are $2$ and $2^k - 1$.
  have h₄ : (2 ^ (k - 1) * (2 ^ k - 1)).primeFactors = ⟨{2, 2 ^ k - 1}, by simp [h₁]⟩ := by
    -- We need to show biimplication.
    ext q
    simp [h₂]
    constructor
    . -- If $q$ is a prime factor of $N$, then $q$ is either $2$ or $2^k - 1$.
      rintro ⟨hq, h₁⟩
      rw [Nat.Prime.dvd_mul hq] at h₁
      -- Since $q$ is prime, it must either divide $2^{k-1}$ or $2^k - 1$.
      rcases h₁ with h₁ | h₁
      . -- If $q$ divides $2^{k-1}$, then $q = 2$.
        left
        apply Nat.Prime.dvd_of_dvd_pow hq at h₁
        rwa [Nat.prime_dvd_prime_iff_eq hq Nat.prime_two] at h₁
      . -- If $q$ divides $2^k - 1$, then $q = 2^k - 1$.
        right
        exact (Nat.prime_dvd_prime_iff_eq hq h).mp h₁
    . -- We show both $2$ and $2^k - 1$ are prime factors of $N$.
      rintro (rfl | rfl)
      . simp only [Nat.prime_two, true_and]
        suffices 2 ∣ 2 ^ (k - 1) from Dvd.dvd.mul_right this (2 ^ k - 1)
        refine dvd_pow_self 2 (by simp [Nat.sub_ne_zero_iff_lt, hk'])
      . simp only [h, dvd_mul_left, and_self]
  -- We need to show that the sum of the factors of $N$ is equal to $2N$.
  suffices H : ∑ i ∈ (2 ^ (k - 1) * (2 ^ k - 1)).divisors, i = 2 * (2 ^ (k - 1) * (2 ^ k - 1)) by
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, two_mul] at H
    apply add_right_cancel H
  -- We use the fact that the sum of the factors of $N$ is equal to (1 + p₁ + p₁ ^ 2 + ... + p₁ ^ (k₁ - 1)) * (1 + p₂ + p₂ ^ 2 + ... + p₂ ^ (k₂ - 1)) * ... * (1 + pₙ + pₙ ^ 2 + ... + pₙ ^ (kₙ - 1))
  rw [Nat.sum_divisors h₃.ne', h₄]
  simp [Finset.prod]
  -- We compute the factorization of $N$.
  have H₁ : (2 ^ (k - 1) * (2 ^ k - 1)).factorization 2 = k - 1 := by
    -- $v_2(N) = v_2(2^{k-1}) + v_2(2^k - 1) = k - 1 + 0 = k - 1$.
    rw [Nat.factorization_def _ Nat.prime_two, padicValNat.mul (by positivity) (by positivity), padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd, Nat.add_zero]
    . refine Odd.not_two_dvd_nat ?_
      exact Nat.Prime.odd_of_ne_two h (Ne.symm h₁)
  have H₂ : (2 ^ (k - 1) * (2 ^ k - 1)).factorization (2 ^ k - 1) = 1 := by
    have inst : Fact (2 ^ k - 1).Prime := ⟨h⟩
    -- $v_{2^k - 1}(N) = v_{2^k - 1}(2^{k-1}) + v_{2^k - 1}(2^k - 1) = 0 + 1 = 1$.
    rw [Nat.factorization_def _ h, padicValNat.mul (by positivity) (by positivity), padicValNat.pow _ (by simp), padicValNat.eq_zero_of_not_dvd (by simpa [Nat.prime_dvd_prime_iff_eq h Nat.prime_two] using Ne.symm h₁), padicValNat.self (Nat.Prime.one_lt h), Nat.mul_zero]
  rw [H₁, H₂]
  -- We use the formula for the sum of a geometric series.
  -- After simplifying, we get the desired result.
  simp [hk, Nat.one_le_two_pow, Nat.geomSum_eq, ← mul_assoc, ← pow_succ']
  exact Nat.mul_comm _ _