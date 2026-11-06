import Mathlib

open ArithmeticFunction Finset Nat

/- Un entier $n$ est parfait si la somme de ses diviseurs est 2 n .
Soit n un entier parfait et $p$ son plus petit diviseur premier.
Montrer que l'exposant de $p$ dans la décomposition en produit de puissances de nombres premiers de n est pair. -/
theorem number_theory_607210 {n : ℕ} (hn : ∑ d ∈ n.divisors, d = 2 * n) (p : ℕ)
    (n_not_6: n ≠ 6)
    (hp : p.Prime ∧ p ∣ n ∧ ∀ x, x.Prime → x ∣ n → x ≥ p) :
    Even (Nat.factorization n p) := by
  -- n = 0 case is trivial. notice that ordinary definition of perfect number require n > 0,
  -- but the definition here allows n=0.
  by_cases nnz: n = 0
  · simp [nnz]

  -- now n ≠ 0.

  -- n = p^i × q, with p and q are coprime.
  obtain ⟨q, hq, co⟩ : ∃ q, n = p^(n.factorization p) * q ∧ Nat.Coprime p q := by
    use (n / p^(n.factorization p))
    constructor
    · exact (ordProj_mul_ordCompl_eq_self n p).symm
    · apply coprime_ordCompl hp.left nnz

  -- consider sum of divisor of n.
  -- σ (n) = ∏ (1 + p_i + p_i^2 + p_i^(e_i)),
  -- so (1+p+p^2+..+p^(e_i)) ∣ σ (n) = 2n
  have h1: ∑ k ∈ range (n.factorization p + 1), p^k ∣ 2*n := by
    rw [← hn, ← sigma_one_apply]
    -- σ is mutiplicative
    nth_rw 2 [hq]
    replace co: (p^(n.factorization p)).Coprime q := by
      exact Coprime.pow_left (n.factorization p) co
    rw [IsMultiplicative.map_mul_of_coprime isMultiplicative_sigma co]
    -- thus suffices to prove (1+p+...+p^e) ∣ σ (p^e), and they are equal.
    rw [← sigma_one_apply_prime_pow hp.left]
    apply Nat.dvd_mul_right

  -- suppose on the contrary, power index of p in n is not even.
  rw [← not_odd_iff_even]
  rintro hodd

  -- then we have p+1 divide (1+p+..+p^e)
  have h2: p+1 ∣ ∑ k ∈ range (n.factorization p + 1), p^k := by
    rcases (odd_iff_exists_bit1.mp hodd) with ⟨k, hk⟩
    -- 1+p+p^2+...+p^(2k+1) = (1+p) + (1+p)p^2 + ... + (1+p)p^(2k)
    have: ∑ i ∈ range (2*k+1+1), p^i = (1+p) *
      ∑ i ∈ range (k+1), p^(2*i) := by
      clear * -
      induction' k with k ih
      · simp [add_comm]
      · have: 2*(k+1) +1 + 1 = (2*k+1+1) + 1 + 1 := by ring
        rw [this, sum_range_succ _ (2*k+1+1+1),
        sum_range_succ _ (2*k+1+1), ih,
        sum_range_succ _ (k+1), add_assoc, mul_add]
        ring
    rw [hk, this, add_comm p 1]
    apply dvd_mul_right

  -- combine h1 and h2, 1+p divide 2n.
  have h3: p+1 ∣ 2*n := Nat.dvd_trans h2 h1

  -- cases on whether p is 2 or odd prime.
  rcases (Prime.eq_two_or_odd' hp.left) with peq2 | podd

  · -- p =2, then p+1 = 3. n has factor 2,3,
    -- then 2,3,6 are all factors of n.
    have dvd2: 2 ∣ n := by
      rw [← peq2]
      apply hp.right.left
    have dvd3: 3 ∣ n := by
      simp only [peq2, reduceAdd] at h3
      rw [Nat.Prime.dvd_mul (by norm_num)] at h3
      norm_num at h3
      exact h3
    have dvd6: 6 ∣ n := by
      have := Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) dvd2 dvd3
      simpa
    have: {n, n/2, n/3, n/6, n/n} ⊆ n.divisors := by
      intro _
      simp only [mem_insert, mem_singleton, mem_divisors, ne_eq]
      rintro (h | h | h | h | h)
      all_goals
        refine ⟨?_, nnz⟩
        rw [h]
      all_goals
        apply div_dvd_of_dvd ?_
        simp [dvd2, dvd3, dvd6]

    -- therefore sum of divisors of n is at least n + n/2 + n/3 + n/6 + 1.
    -- but n + n/2 + n/3 + n/6 + 1 = 2n + 1, contradiction.
    replace: ∑ d ∈ {n, n/2, n/3, n/6, 1}, d ≤ ∑ d ∈ n.divisors, d := by
      have h: n/n = 1 := by
        refine Nat.div_self ?_
        exact zero_lt_of_ne_zero nnz
      rw [h] at this
      apply Finset.sum_le_sum_of_subset this
    rw [hn, Finset.sum_insert, Finset.sum_insert,
    Finset.sum_insert, Finset.sum_insert] at this
    simp only [sum_singleton] at this
    rify at this; zify at dvd2 dvd3 dvd6
    rw [Int.cast_div dvd2 (by norm_num), Int.cast_div dvd3 (by norm_num),
    Int.cast_div dvd6 (by norm_num)] at this
    push_cast at this
    linarith only [this]
    -- prove 1, n/6, n/2, n/3 are pairwise distinct
    -- notice that when n = 6, n/6 = 1. they are not pairwise distinct.
    -- and given n ≠ 6, we can derive a contradiction.
    all_goals
      simp only [mem_insert, mem_singleton, not_or]
      omega

  · -- p ≠ 2, then p+1 is even, p+1 / 2 divide n.
    have dvd2: 2 ∣ p+1 := even_iff_two_dvd.mp (Odd.add_one podd)
    have h4: (p+1)/2 ∣ n := by
      exact (div_dvd_iff_dvd_mul dvd2 (by norm_num)).mpr h3
    -- p > 3, then (p+1)/2 > 1.
    have h5: (p+1)/2 > 1 := by
      rify; zify at dvd2
      rw [Int.cast_div dvd2 (by norm_num)]
      push_cast
      have: p ≥ 3 := by
        have hh1 := hp.left.two_le
        have hh2: p ≠ 2 := by omega
        have hh3 := lt_of_le_of_ne hh1 hh2.symm
        exact hh3
      rify at this
      linarith only [this]
    -- then exist prime q divide (p+1)/2
    rcases (exists_prime_and_dvd h5.ne') with ⟨q, hq⟩
    -- this q also divide n, since (p+1)/2 divide n.
    have qdvd: q ∣ n := by
      apply dvd_trans hq.right h4
    -- but we already suppose p the least prime divisor, contradiction.
    have hq1 := hp.right.right q hq.left qdvd
    have hq2: q < p := by
      have hh1: q ≤ (p+1)/2 := by
        apply le_of_dvd ?_ hq.right
        apply lt_trans (by norm_num) h5
      omega
    linarith only [hq1, hq2]