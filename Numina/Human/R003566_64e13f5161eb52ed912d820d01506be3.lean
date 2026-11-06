import Mathlib

-- 2. (5 points) Two different natural numbers end with 9 zeros and have exactly 110 divisors. Find their sum.

lemma factorization_prod_pow_eq_self {n : ℕ} (hn: n ≠ 0):
  n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hn]
  rfl

lemma prod_eq_one_iff {s : Finset ℕ} {f : ℕ → ℕ} : ∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1 := by
  induction' s using Finset.cons_induction with i s hi ih <;> simp [*]

lemma triple_product_eq_110 {a b c : ℕ} (ha: 10 ≤ a) (hb: 10 ≤ b) (hc: 1 ≤ c):
   (a * b * c = 110) → (a = 11 ∧ b = 10 ∧ c = 1) ∨ (a = 10 ∧ b = 11 ∧ c = 1) := by
  intro h
  have ha': a ≤ 11 := by
    by_contra
    have : 120 ≤ a * b := by nlinarith
    nlinarith

  have hc': c = 1 := by
    by_contra h
    have : 2 ≤ c := by omega
    have : 10 ≤ a * b := by nlinarith
    nlinarith
  subst c
  simp
  interval_cases a
  . simp; linarith
  . simp; linarith

lemma factorization_10_9_2 : (10 ^ 9).factorization 2 = 9 := by
  native_decide

lemma factorization_10_9_5 : (10 ^ 9).factorization 5 = 9 := by
  native_decide


theorem number_theory_196023 :
  {n | 10^9 ∣ n ∧ n.divisors.card = 110} = {2 * 10 ^ 9, 5 * 10 ^ 9} ∧ 2 * 10 ^ 9 + 5 * 10 ^ 9 = 7 * 10 ^ 9 := by
  refine ⟨?_, by norm_num⟩
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  . intro ⟨⟨k, hk⟩, hcard⟩
    have hn0 : n ≠ 0 := by
      by_contra h
      rw [h] at hcard
      simp at hcard

    have hk0 : k ≠ 0 := by
      by_contra h
      rw [h] at hk
      simp at hk
      contradiction

    rw [Nat.card_divisors hn0] at hcard

    have h2_in_factors : 2 ∈ n.primeFactors := by
      simp
      refine ⟨?_, ?_, ?_⟩
      . norm_num
      . omega
      . omega

    have := Finset.mul_prod_erase n.primeFactors (fun x => n.factorization x + 1) h2_in_factors
    simp at this
    rw [← this] at hcard

    have h5_in_factors': 5 ∈ n.primeFactors.erase 2 := by
      simp
      refine ⟨?_, ?_, ?_⟩
      . norm_num
      . omega
      . omega

    have := Finset.mul_prod_erase (n.primeFactors.erase 2) (fun x => n.factorization x + 1) h5_in_factors'
    simp at this
    rw [← this] at hcard
    rw [← mul_assoc] at hcard

    apply triple_product_eq_110 at hcard
    . rcases hcard with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      . left
        replace h1 : n.factorization 2 = 10 := by omega
        replace h2 : n.factorization 5 = 9 := by omega
        rw [prod_eq_one_iff] at h3

        rw [factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
        have := Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) h2_in_factors
        simp at this
        rw [← this, h1]

        have := Finset.mul_prod_erase (n.primeFactors.erase 2) (fun p => p ^ n.factorization p) h5_in_factors'
        simp at this
        rw [← this, h2]

        suffices ∏ x ∈ (n.primeFactors.erase 2).erase 5, x ^ n.factorization x = 1 by
          rw [this]
          ring
        rw [prod_eq_one_iff]
        intro x hx
        specialize h3 x hx
        have : n.factorization x = 0 := by omega
        rw [this]
        simp
            
      . right
        replace h1 : n.factorization 2 = 9 := by omega
        replace h2 : n.factorization 5 = 10 := by omega
        rw [prod_eq_one_iff] at h3

        rw [factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
        have := Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) h2_in_factors
        simp at this
        rw [← this, h1]

        have := Finset.mul_prod_erase (n.primeFactors.erase 2) (fun p => p ^ n.factorization p) h5_in_factors'
        simp at this
        rw [← this, h2]

        suffices ∏ x ∈ (n.primeFactors.erase 2).erase 5, x ^ n.factorization x = 1 by
          rw [this]
          ring
        rw [prod_eq_one_iff]
        intro x hx
        specialize h3 x hx
        have : n.factorization x = 0 := by omega
        rw [this]
        simp
    . rw [hk]
      rw [Nat.factorization_mul (by norm_num) hk0, Finsupp.add_apply]
      rw [factorization_10_9_2]
      omega
    . rw [hk]
      rw [Nat.factorization_mul (by norm_num) hk0, Finsupp.add_apply]
      rw [factorization_10_9_5]
      omega
    . suffices 0 < ∏ x ∈ (n.primeFactors.erase 2).erase 5, (n.factorization x + 1) by omega
      apply Finset.prod_pos
      intro i hi
      omega

  . rintro (rfl | rfl)
    . constructor
      . use 2; ring
      . rw [Nat.card_divisors (by norm_num)]
        native_decide
    . constructor
      . use 5; ring
      . rw [Nat.card_divisors (by norm_num)]
        native_decide
