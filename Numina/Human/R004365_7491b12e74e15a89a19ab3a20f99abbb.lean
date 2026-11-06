import Mathlib

set_option exponentiation.threshold 2018
-- Determine all natural numbers n that are less than $128^{97}$ and have exactly 2019 divisors.

-- (Richard Henner)

-- Answer. There are 4 solutions: $n=2^{672} \cdot 3^{2}$ or $n=2^{672} \cdot 5^{2}$ or $n=2^{672} \cdot 7^{2}$ or $n=2^{672} \cdot 11^{2}$.

lemma factorization_prod_pow_eq_self {n : ℕ} (hn: n ≠ 0):
  n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hn]
  rfl

lemma two_le_prime {p : ℕ} (hp: p.Prime) : 2 ≤ p := by
  contrapose hp
  interval_cases p <;> decide

lemma divisors_of_2019: Nat.divisors 2019 = {1, 3, 673, 2019} := by
  native_decide

lemma divisors_card_eq_2019_of_p1_p2 (p1 p2: ℕ) (hp1ne2: p1 ≠ p2) (h_p1_prime: p1.Prime) (h_p2_prime: p2.Prime) :
  (p1 ^ 672 * p2 ^ 2).divisors.card = 2019 := by
  let n := p1 ^ 672 * p2 ^ 2
  have hn_ne_zero : n ≠ 0 := by 
    unfold n
    by_contra h
    norm_num at h
    rcases h with h | h
    . contrapose h_p1_prime
      rw [h]
      decide
    . contrapose h_p2_prime
      rw [h]
      decide

  have hn_prime_factors: n.primeFactors = {p1, p2} := by
    ext p
    simp
    constructor
    . rintro ⟨h_p_prime, h_p_dvd_n, _⟩
      unfold n at h_p_dvd_n
      rw [Nat.dvd_mul] at h_p_dvd_n
      obtain ⟨y, z, hy, hz, h_yz_eq_p⟩ := h_p_dvd_n
      have : y ∣ p := by use z; rw [h_yz_eq_p]
      rw [Nat.dvd_prime h_p_prime] at this
      rcases this with h | h
      . right
        have : z = p := by nlinarith
        rw [this] at hz
        exact Nat.prime_eq_prime_of_dvd_pow h_p_prime h_p2_prime hz
      . left
        rw [h] at hy
        exact Nat.prime_eq_prime_of_dvd_pow h_p_prime h_p1_prime hy

    . rintro (h1 | h2)
      . refine ⟨?_, ?_, ?_⟩
        . rw [h1]; exact h_p1_prime
        . use p1 ^ 671 * p2 ^ 2
          unfold n
          rw [h1]
          ring
        . exact hn_ne_zero
      . refine ⟨?_, ?_, ?_⟩
        . rw [h2]; exact h_p2_prime
        . use p1 ^ 672 * p2
          unfold n
          rw [h2]
          ring
        . exact hn_ne_zero

  have h_p1_pow_ne_zero: p1 ^ 672 ≠ 0 := by
    by_contra h
    simp at h
    have : n = 0 := by unfold n; rw [h]; simp
    contradiction

  have h_p2_pow_ne_zero: p2 ^ 2 ≠ 0 := by
    by_contra h
    simp at h
    have : n = 0 := by unfold n; rw [h]; simp
    contradiction

  have hn_factorization_p1: n.factorization p1 = 672 := by
    unfold n
    rw [Nat.factorization_mul h_p1_pow_ne_zero h_p2_pow_ne_zero]
    simp
    rw [Nat.Prime.factorization h_p1_prime]
    simp
    apply Nat.factorization_eq_zero_of_not_dvd
    by_contra h_contra
    rw [Nat.dvd_prime h_p2_prime] at h_contra
    rcases h_contra with h | h
    . rw [h] at h_p1_prime
      contrapose h_p1_prime
      decide
    . contradiction

  have hn_factorization_p2: n.factorization p2 = 2 := by
    unfold n
    rw [Nat.factorization_mul h_p1_pow_ne_zero h_p2_pow_ne_zero]
    simp
    rw [Nat.Prime.factorization h_p2_prime]
    simp
    apply Nat.factorization_eq_zero_of_not_dvd
    by_contra h_contra
    rw [Nat.dvd_prime h_p1_prime] at h_contra
    rcases h_contra with h | h
    . rw [h] at h_p2_prime
      contrapose h_p2_prime
      decide
    . rw [h] at hp1ne2
      contradiction

  rw [Nat.card_divisors hn_ne_zero, hn_prime_factors]
  rw [Finset.prod_pair hp1ne2]
  rw [hn_factorization_p1, hn_factorization_p2]
  norm_num

lemma one_le_n_factorization_p {n p : ℕ} (hp: p ∈ n.primeFactors) : 
  1 ≤ n.factorization p := by
  simp at hp
  apply Nat.Prime.factorization_pos_of_dvd hp.1 hp.2.2 hp.2.1

theorem number_theory_257575 :
  {n : ℕ | n < 128 ^ 97 ∧ n.divisors.card = 2019} = {2^672 * 3^2, 2^672 * 5^2, 2^672 * 7^2, 2^672 * 11^2} := by
  ext n
  rw [Set.mem_setOf_eq]
  constructor
  . rintro ⟨h1, h2⟩
    have hn_ne_zero : n ≠ 0 := by
      by_contra h
      rw [h] at h2
      simp at h2

    have h_factor_card_neq_1 : n.primeFactors.card ≠ 1 := by
      by_contra h_contra
      rw [Finset.card_eq_one] at h_contra
      obtain ⟨p, hp⟩ := h_contra
      have : n = p ^ 2018 := by
        rw [Nat.card_divisors hn_ne_zero, hp] at h2
        simp at h2
        rw [factorization_prod_pow_eq_self hn_ne_zero, hp]
        simp
        rw [h2]

      rw [this] at h1
      have : 2^2018 ≤ p^2018 := by
        apply Nat.pow_le_pow_left
        have : p ∈ n.primeFactors := by rw [hp]; simp
        simp at this
        exact two_le_prime this.1

      have : 2 ^ 2018 < 128 ^ 97 := by linarith
      omega

    have h_factor_card_le_2 : n.primeFactors.card ≤ 2 := by
      by_contra h_contra
      simp at h_contra
      rw [Finset.two_lt_card_iff] at h_contra
      obtain ⟨p1, p2, p3, hp1, hp2, hp3, hp1_ne_p2, hp1_ne_p3, hp2_ne_p3⟩ := h_contra
      rw [Nat.card_divisors hn_ne_zero] at h2
      have : ∃ a b c d, 2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c ∧ 1 ≤ d ∧ a * (b * c * d) = 2019 := by
        rw [← h2]
        have := Finset.mul_prod_erase n.primeFactors (fun x => n.factorization x + 1) hp1
        simp at this
        rw [← this]
        have : p2 ∈ n.primeFactors.erase p1 := by
          simp
          refine ⟨?_, ?_, ?_, ?_⟩
          . exact Ne.symm hp1_ne_p2
          . simp at hp2; exact hp2.1
          . simp at hp2; exact hp2.2.1
          . exact hn_ne_zero
        have := Finset.mul_prod_erase (n.primeFactors.erase p1) (fun x => n.factorization x + 1) this
        simp at this
        rw [← this]
        have : p3 ∈ (n.primeFactors.erase p1).erase p2 := by
          simp
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          . exact Ne.symm hp2_ne_p3
          . exact Ne.symm hp1_ne_p3
          . simp at hp3; exact hp3.1
          . simp at hp3; exact hp3.2.1
          . exact hn_ne_zero
          
        have := Finset.mul_prod_erase ((n.primeFactors.erase p1).erase p2) (fun x => n.factorization x + 1) this
        simp at this
        rw [← this]
        use n.factorization p1 + 1, n.factorization p2 + 1, n.factorization p3 + 1, ∏ x ∈ ((n.primeFactors.erase p1).erase p2).erase p3, (n.factorization x + 1)
        simp
        refine ⟨one_le_n_factorization_p hp1, one_le_n_factorization_p hp2, one_le_n_factorization_p hp3, ?_, by ring⟩
        apply Finset.one_le_prod'
        intro i hi
        omega
        
      obtain ⟨a, b, c, d, ha, hb, hc, hd, h_abcd_eq_2019⟩ := this
      have h_not_prime: ¬ (∃ p, p.Prime ∧ b*c*d = p) := by
        simp
        rw [Nat.prime_def]
        simp
        intro h
        use b
        refine ⟨?_, ?_, ?_⟩
        . use c * d
          ring
        . omega
        . by_contra h_contra
          have : 2 ≤ c * d := by nlinarith
          nlinarith

      have : a ∈ Nat.divisors 2019 := by
        simp
        use (b * c * d)
        rw [h_abcd_eq_2019]

      rw [divisors_of_2019] at this
      simp at this
      rcases this with h | h | h | h
      . rw [h] at ha
        norm_num at ha
      . contrapose h_not_prime
        simp
        have : b * c * d = 673 := by nlinarith
        rw [this]
        native_decide
      . contrapose h_not_prime
        simp
        have : b * c * d = 3 := by nlinarith
        rw [this]
        native_decide
      . have : b * c * d = 1 := by nlinarith
        have : 4 ≤ b * c := by nlinarith
        nlinarith

    have h_factor_card_eq_2 : n.primeFactors.card = 2 := by
      by_contra h_contra
      have : n.primeFactors.card = 0 := by omega
      simp at this
      rcases this with h | h
      . contradiction
      . rw [h] at h2
        simp at h2

    have h_p1_p2_form_n: ∃ p1 p2, n = p1 ^ 672 * p2 ^ 2 ∧ p1 ≠ p2 ∧ p1.Prime ∧ p2.Prime := by
      rw [Finset.card_eq_two] at h_factor_card_eq_2
      obtain ⟨p1, p2, hp1ne2, hpset⟩ := h_factor_card_eq_2

      have ⟨h_p1_prime, h_p1_dvd_n⟩: p1.Prime ∧ p1 ∣ n := by
        have : p1 ∈ n.primeFactors := by rw [hpset]; simp
        simp at this
        exact ⟨this.1, this.2.1⟩

      have ⟨h_p2_prime, h_p2_dvd_n⟩: p2.Prime ∧ p2 ∣ n := by
        have : p2 ∈ n.primeFactors := by rw [hpset]; simp
        simp at this
        exact ⟨this.1, this.2.1⟩

      rw [Nat.card_divisors hn_ne_zero, hpset] at h2
      rw [Finset.prod_pair hp1ne2] at h2

      have : (n.factorization p1 + 1) ∈ Nat.divisors 2019 := by
        simp
        use (n.factorization p2 + 1)
        rw [h2]

      rw [divisors_of_2019] at this
      simp at this
      rcases this with h | h | h | h
      . suffices 0 < n.factorization p1 by omega
        apply Nat.Prime.factorization_pos_of_dvd
        . exact h_p1_prime
        . exact hn_ne_zero
        . exact h_p1_dvd_n
      . use p2, p1
        refine ⟨?_, Ne.symm hp1ne2, h_p2_prime, h_p1_prime⟩
        rw [factorization_prod_pow_eq_self hn_ne_zero, hpset, Finset.prod_pair hp1ne2]
        have : n.factorization p2 = 672 := by nlinarith
        rw [h, this]
        ring

      . use p1, p2
        refine ⟨?_, hp1ne2, h_p1_prime, h_p2_prime⟩
        rw [factorization_prod_pow_eq_self hn_ne_zero, hpset, Finset.prod_pair hp1ne2]
        have : n.factorization p2 = 2 := by nlinarith
        rw [h, this]

      . rw [h] at h2
        suffices 0 < n.factorization p2 by omega
        apply Nat.Prime.factorization_pos_of_dvd
        . exact h_p2_prime
        . exact hn_ne_zero
        . exact h_p2_dvd_n

    obtain ⟨p1, p2, h_p1_p2_form_n, hp1ne2, h_p1_prime, h_p2_prime⟩ := h_p1_p2_form_n

    have := two_le_prime h_p2_prime
    have h_p1_eq_2 : p1 = 2 := by
      by_contra h_contra
      have := two_le_prime h_p1_prime
      have : 3 ^ 672 ≤ p1 ^ 672 := by
        apply Nat.pow_le_pow_left
        omega
      nlinarith

    have h_p2_le_11 : p2 ≤ 11 := by
      by_contra h_contra
      rw [h_p1_p2_form_n, h_p1_eq_2] at h1
      have : 12^2 ≤ p2^2 := by
        apply Nat.pow_le_pow_left
        omega
      nlinarith

    interval_cases p2
    . contradiction
    . left; rw [h_p1_p2_form_n, h_p1_eq_2]
    . contrapose h_p2_prime; decide
    . right; left; rw [h_p1_p2_form_n, h_p1_eq_2]
    . contrapose h_p2_prime; decide
    . right; right; left; rw [h_p1_p2_form_n, h_p1_eq_2]
    . contrapose h_p2_prime; decide
    . contrapose h_p2_prime; decide
    . contrapose h_p2_prime; decide
    . right; right; right; rw [h_p1_p2_form_n, h_p1_eq_2]; simp

  . intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl
    . refine ⟨by decide, ?_⟩
      apply divisors_card_eq_2019_of_p1_p2 2 3
      . norm_num
      . decide
      . decide
    . refine ⟨by decide, ?_⟩
      apply divisors_card_eq_2019_of_p1_p2 2 5
      . norm_num
      . decide
      . decide
    . refine ⟨by decide, ?_⟩
      apply divisors_card_eq_2019_of_p1_p2 2 7
      . norm_num
      . decide
      . decide
    . refine ⟨by decide, ?_⟩
      apply divisors_card_eq_2019_of_p1_p2 2 11
      . norm_num
      . decide
      . decide
