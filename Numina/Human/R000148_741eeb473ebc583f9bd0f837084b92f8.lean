import Mathlib

/- σ(n) is sum of divisors of n -/
abbrev σ (n : ℕ) : ℕ := n.divisors.sum id

/- formula to calculate σ(n) -/
lemma σ_eq (n : ℕ) (hn : n > 0) : σ n = ∏ x ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization x + 1), x ^ i := by
  rw [σ]
  exact Nat.sum_divisors (by linarith [hn])

/- define k-perfect -/
abbrev is_k_perfect (k : ℕ) (n : ℕ) : Prop := σ n = k * n

/- Auxiliary Lemma for the Sum of a Geometric Series -/
lemma l_sum_2pow (k : ℕ) : ∑ i ∈ Finset.range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ik =>
    rw [Finset.range_succ, Finset.sum_insert]
    rw [ik]
    rw [(Nat.add_sub_assoc Nat.one_le_two_pow (2 ^ (k + 1))).symm]
    rw [Nat.two_pow_succ (k + 1)]
    exact Finset.not_mem_range_self

/-
An integer $ n $ is called $ k $-perfect if the sum of its divisors $ \sigma(n) $ equals $ k $ times $ n $. It is noted that a perfect number is a 2-perfect number. The tasks are as follows:
a) Show that $ 120 = 2^{3} \cdot 3 \cdot 5 $ is 3-perfect.
-/
theorem number_theory_4922_1 : is_k_perfect 3 120 := rfl

/-
An integer $ n $ is called $ k $-perfect if the sum of its divisors $ \sigma(n) $ equals $ k $ times $ n $. It is noted that a perfect number is a 2-perfect number. The tasks are as follows:
b) Show that $ 30240 = 2^{5} \cdot 3^{2} \cdot 5 \cdot 7 $ is 4-perfect.
-/
theorem number_theory_4922_2 : is_k_perfect 4 30240 := by native_decide


/-
An integer $ n $ is called $ k $-perfect if the sum of its divisors $ \sigma(n) $ equals $ k $ times $ n $. It is noted that a perfect number is a 2-perfect number. The tasks are as follows:
c) Show that $ 14182439040 = 2^{7} \cdot 3^{4} \cdot 5 \cdot 7 \cdot 11^{2} \cdot 17 \cdot 19 $ is 5-perfect.
-/
theorem number_theory_4922_3 : is_k_perfect 5 14182439040 := by
  rw [is_k_perfect, σ_eq 14182439040 (Nat.zero_lt_succ 14182439039)]
  native_decide

/-
An integer $ n $ is called $ k $-perfect if the sum of its divisors $ \sigma(n) $ equals $ k $ times $ n $. It is noted that a perfect number is a 2-perfect number. The tasks are as follows:
d) Find all 3-perfect numbers of the form $ n = 2^{k} \cdot 3 \cdot p $, where $ p $ is an odd prime.
-/
theorem number_theory_4922_4
      (n k p : ℕ)
      (hn : n = 2 ^ k * 3 * p)
      (hk : k > 0)
      (hp : Nat.Prime p)
      (hp_odd : 2 ≠ p ∧ 3 ≠ p)
      (h_top : is_k_perfect 3 n)
      : (2 ^ (k + 1) - 1) * 4 * (p + 1) = 3 * (2 ^ k * 3 * p) := by
-- The provided solution is prooblematic, it didn't consider the cases where p = 3 or k = 0
-- For now, just consider k > 0 and p > 3
  have h_n_ne_zero : n ≠ 0 := by
    rw [hn]
    apply mul_ne_zero_iff.mpr
    exact ⟨by norm_num, Nat.Prime.ne_zero hp⟩
  rw [is_k_perfect, σ_eq n (Nat.zero_lt_of_ne_zero h_n_ne_zero)] at h_top

  have h_n_pfactors : n.primeFactors = {2, 3, p} := by
    rw [hn, Nat.primeFactors_mul (by norm_num) (Nat.Prime.ne_zero hp),
        Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow,
        Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three, Nat.Prime.primeFactors hp]
    . rfl
    . linarith

  have h_nfac2 : n.factorization 2 = k := by
    rw [hn, mul_assoc, Nat.factorization_mul ((NeZero.ne' (2 ^ k)).symm) (show 3 * p ≠ 0 by simp [Nat.Prime.ne_zero hp]),
      Nat.factorization_mul (show 3 ≠ 0 by norm_num) (Nat.Prime.ne_zero hp)]
    norm_num
    have : ¬ 2 ∣ p := by
      apply Odd.not_two_dvd_nat
      apply (Nat.Prime.odd_of_ne_two hp (by omega))
    exact Nat.factorization_eq_zero_of_not_dvd this

  have h_nfac3 : n.factorization 3 = 1 := by
    rw [hn, mul_assoc, Nat.factorization_mul ((NeZero.ne' (2 ^ k)).symm) (show 3 * p ≠ 0 by simp [Nat.Prime.ne_zero hp]),
      Nat.factorization_mul (show 3 ≠ 0 by norm_num) (Nat.Prime.ne_zero hp)]
    norm_num
    have hpge3 : p > 3 := by
      obtain ⟨hpne2, hpne3⟩ := hp_odd
      have hpgt1 : p > 1 := by exact Nat.Prime.one_lt hp
      omega
    have : ¬ 3 ∣ p := by
      by_contra hh
      obtain ⟨t, ht⟩ := hh
      have htpos : t > 0 := by
        have : 3 * t > 0 := by
          rw [← ht]
          exact Nat.zero_lt_of_lt hpge3
        exact Nat.pos_of_mul_pos_left this
      have : t ∣ p := by exact Dvd.intro_left 3 (id (Eq.symm ht))
      have : t = 1 := by
        by_contra hkneone
        rw [(Nat.Prime.dvd_iff_eq hp hkneone).mp this] at ht
        have : t ≠ 3 * t := by
          refine Nat.ne_of_lt ?_
          rw [show 3 * t = t + 2 * t by ring]
          refine Nat.lt_add_of_pos_right ?_
          exact Nat.succ_mul_pos 1 htpos
        exact this ht
      rw [this, mul_one] at ht
      exact (Nat.ne_of_lt' hpge3) ht
    exact Nat.factorization_eq_zero_of_not_dvd this

  have h_nfacp: n.factorization p = 1 := by
    rw [hn, mul_assoc, Nat.factorization_mul ((NeZero.ne' (2 ^ k)).symm) (show 3 * p ≠ 0 by simp [Nat.Prime.ne_zero hp]),
      Nat.factorization_mul (show 3 ≠ 0 by norm_num) (Nat.Prime.ne_zero hp)]
    norm_num
    obtain ⟨hpne2, hpne3⟩ := hp_odd
    simp [Finsupp.single_eq_of_ne hpne2, Finsupp.single_eq_of_ne hpne3]
    exact Nat.Prime.factorization_self hp

  -- Use the geometric series sum lemma to show that
  -- (1 + 2 + 4 + ... + 2^k) = (2 ^ (k + 1) - 1)
  have h_sum_2powk : ∑ i ∈ Finset.range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1 := by
    apply l_sum_2pow

  rw [h_n_pfactors] at h_top
  have h1: 2 ∉ ({3, p}:Finset ℕ) := by
    apply Finset.forall_mem_not_eq.mp
    intros b hb
    rw [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb|hb
    . linarith
    . exact ne_of_ne_of_eq hp_odd.1 (id (Eq.symm hb))
  have h2: 3 ∉ {p} := Finset.not_mem_singleton.mpr hp_odd.2
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_singleton,
    h_nfac2, h_nfac3, h_nfacp, h_sum_2powk] at h_top
  norm_num at h_top
  rw [← mul_assoc, hn] at h_top
  exact h_top

/-
An integer $ n $ is called $ k $-perfect if the sum of its divisors $ \sigma(n) $ equals $ k $ times $ n $. It is noted that a perfect number is a 2-perfect number. The tasks are as follows:
e) Show that if $ n $ is 3-perfect and $ 3 \nmid n $, then $ 3n $ is 4-perfect.
-/
theorem number_theory_4922_5
    (n : ℕ)
    (hn : is_k_perfect 3 n ∧ Nat.Coprime 3 n)
    : is_k_perfect 4 (3 * n) := by
  -- The provided solution lacks a detailed process
  -- Since σ is a multiplicative function and 3 is coprime with n, we get σ (3 * n) = σ 3 * σ n
  have h_sigma_3n: σ (3 * n) = σ 3 * σ n := Nat.Coprime.sum_divisors_mul hn.right
  have h_sigma_3 : σ 3 = 4 := by native_decide
  have h_sigma_n : σ n = 3 * n := hn.left
  rw [is_k_perfect, h_sigma_3n, h_sigma_3, h_sigma_n]
