import Mathlib

/- 12. (ITA) Let $p$ be a prime number and let $f(x)$ be a polynomial of degree $d$ with integer coefficients such that: (i) $f(0)=0, f(1)=1$; (ii) for every positive integer $n$, the remainder of the division of $f(n)$ by $p$ is either 0 or 1. Prove that $d \geq p-1$. -/
theorem number_theory_24750 {p : ℕ} (hp : Nat.Prime p)
    (f : Polynomial ℤ) (hf0 : f.eval 0 = 0) (hf1 : f.eval 1 = 1)
    (hpn : ∀ n > 0, f.eval n % p = 0 ∨ f.eval n % p = 1) :
    f.natDegree ≥ p - 1 := by
  -- We'll prove this by contradiction.
  -- Assume that the degree of f is less than p-1.
  by_contra! h1
  -- Lemma: for any polynomial of degree less than p-1,
  -- the sum of its values at 0, 1, ..., p-1 is divisible by p.
  have h2 : (∑ i in Finset.Icc 0 (p - 1), f.eval (i : ℤ)) % p = 0 := by
    -- We first express the polynomial evaluation as a sum of terms
    conv => lhs; arg 1; arg 2; intro i; rw [Polynomial.eval_eq_sum_range' h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_int_mod]
    convert Int.zero_emod _
    apply Finset.sum_eq_zero
    intro k hk
    suffices (∑ i ∈ Finset.Icc 0 (p - 1), (i : ℤ) ^ k) % p = 0 by
      simp [Int.mul_emod, this]
    simp at hk
    -- Now it is enough to show that for each power k ≤ degree of f < p-1,
    -- the sum of i^k for i from 0 to p-1 is divisible by p
    let S (k : ℕ) := (∑ i ∈ Finset.range p, (i : ℤ) ^ k)
    have hS : ∀ k, S k = ∑ i ∈ Finset.Icc 0 (p - 1), (i : ℤ) ^ k := by
      intro k
      simp [S]
      congr
      ext x
      simp
      omega
    rw [← hS]
    -- We'll prove by strong induction that S(k) ≡ 0 (mod p) for all k < p-1
    induction' k using Nat.strong_induction_on with k ih
    -- Note that(k+1)S_k + Σ(binomial(k+1,i)S_i) = Σ((n+1)^(k+1) - n^(k+1))
    have h2 : (k + 1) * S k + ∑ i ∈ Finset.range k, Nat.choose (k + 1) i * S i = ∑ n ∈ Finset.range p, ((n + 1 : ℤ) ^ (k + 1) - n^(k + 1)) := by
      simp_rw [add_pow, Finset.sum_range_succ (n := k + 1)]
      simp
      rw [Finset.sum_comm, Finset.sum_range_succ]
      simp
      rw [← Finset.sum_mul, add_comm]
      congr 1
      swap
      · rw [mul_comm]
      congr
      ext i
      rw [Finset.mul_sum]
      congr
      ext j
      ring
    -- The right side telescopes to p^(k+1)
    have h3 : ∑ n ∈ Finset.range p, ((n + 1 : ℤ) ^ (k + 1) - n^(k + 1)) = p^(k + 1) := by
      let f := fun (i : ℕ) ↦ (i : ℤ) ^ (k + 1)
      change ∑ n ∈ Finset.range p, (f (n + 1) - f n) = p ^ (k + 1)
      rw [Finset.sum_range_sub]
      simp [f]
    rw [h3] at h2
    -- So we have: (k+1)S_k + Σ(binomial(k+1,i)S_i) ≡ 0 (mod p)
    replace h2 : (((k : ℤ) + 1) * S k + ∑ i ∈ Finset.range k, ↑((k + 1).choose i) * S i) % p = 0 := by
      rw [h2]
      simp
      apply dvd_pow_self
      omega
    rw [Int.add_emod] at h2
    -- By induction hypothesis, S_i ≡ 0 (mod p) for all i < k
    have : (∑ i ∈ Finset.range k, ((k + 1).choose i) * S i : ℤ) % p = 0 := by
      rw [Finset.sum_int_mod]
      convert Int.zero_emod _
      apply Finset.sum_eq_zero
      intro i hi
      simp at hi
      rw [Int.mul_emod, ih]
      · simp
      all_goals omega
    simp [this] at h2
    -- Since (k+1) and p are coprime (as k+1 < p), S_k must be divisible by p,
    -- which completes the proof of the lemma.
    simp
    apply Int.dvd_of_dvd_mul_right_of_gcd_one h2
    rw [Int.gcd_eq_one_iff_coprime, Prime.coprime_iff_not_dvd]
    swap
    · exact Nat.prime_iff_prime_int.mp hp
    intro h
    replace h : (p : ℤ) ≤ k + 1 := by apply Int.le_of_dvd _ h; omega
    omega
  -- On the other hand, we know that the sum of f(i) mod p from i=0 to p-1 is positive
  -- because f(0) = 0 and f(1) = 1, and all other values are either 0 or 1 mod p
  have h3 : 0 < ∑ i in Finset.Icc 0 (p - 1), f.eval (i : ℤ) % p := by
    apply Finset.sum_pos'
    · intro i hi
      simp at hi
      cases' i with i
      · simp [hf0]
      specialize hpn (i + 1) (by simp)
      rcases hpn with hpn | hpn <;> simp [hpn]
    · use 1
      simp [hf1]
      constructor
      · omega
      calc
        0 < (1 : ℤ) := by simp
        _ = _ := by
          symm
          rw [Int.emod_eq_of_lt]
          · norm_num
          · omega
  -- Moreover, this sum is less than p since there are at most p - 1 terms equal to 1
  have h4 : (∑ i in Finset.Icc 0 (p - 1), f.eval (i : ℤ) % p) < p := by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (by omega)]
    simp [hf0]
    calc
      ∑ x ∈ Finset.Ioc 0 (p - 1), Polynomial.eval (↑x) f % ↑p ≤ (p - 1) • 1 := by
        convert Finset.sum_le_card_nsmul _ _ _ _
        · simp
        intro i hi
        simp at hi
        cases' i with i
        · simp [hf0]
        specialize hpn (i + 1) (by simp)
        rcases hpn with hpn | hpn <;> simp [hpn]
      _ < p := by
        simp
        omega
  -- This leads to a contradiction, since the sum is divisible by p lies in the interval (0, p).
  rw [Finset.sum_int_mod] at h2
  set v := ∑ i ∈ Finset.Icc 0 (f.natDegree + 1), Polynomial.eval (↑i) f % ↑p
  apply Int.dvd_of_emod_eq_zero at h2
  obtain ⟨k, hk⟩ := h2
  rw [hk] at h3 h4
  have : 0 < k := by nlinarith
  have : k < 1 := by nlinarith
  omega
