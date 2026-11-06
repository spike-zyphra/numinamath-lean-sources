import Mathlib

lemma prime_two : Prime (2 : ℕ) := by
  unfold Prime
  refine ⟨by norm_num, by simp, ?_⟩
  intro a b
  exact (Nat.Prime.dvd_mul (by norm_num)).mp

theorem number_theory_265482 (n : ℕ) (hn : n = 100) :
  {i | i ∈ Set.Icc 1 n ∧ (Nat.divisors i).card % 2 = 1}.ncard / (n:ℝ) = 1 / 10 := by

  have h1 : {i | i ∈ Set.Icc 1 n ∧ (Nat.divisors i).card % 2 = 1} = Finset.filter (fun i => IsSquare i) (Finset.Icc 1 n) := by
    ext x
    simp
    intro hx1 hx2
    unfold IsSquare
    constructor
    . intro h
      contrapose h
      simp at h
      suffices 2 ∣ x.divisors.card by omega
      rw [Nat.card_divisors (by omega)]
      rw [Prime.dvd_finset_prod_iff prime_two]
      by_contra h1
      push_neg at h1
      have h2 : ∀ a, a ∈ x.primeFactors → (x.factorization a) % 2 = 0 := by
        intro a ha
        have := h1 a ha
        omega
      have h3 : (∃ n, x = n ^ 2) := by
        use ∏ p ∈ x.primeFactors, p ^ (x.factorization p / 2)
        rw [← Finset.prod_pow, Finset.prod_congr rfl (fun p hp => by
          rw [← Nat.pow_mul, Nat.div_mul_cancel (by
            have := h2 p hp
            omega
          )]
        )]
        nth_rw 1 [← Nat.factorization_prod_pow_eq_self (show x≠0 by omega)]
        rfl

      rcases h3 with ⟨n, hn⟩
      rw [pow_two] at hn
      have := h n
      contradiction

    . rintro ⟨k, hk⟩


      by_contra h_contra
      have : 2 ∣ x.divisors.card := by omega
      rw [hk, Nat.card_divisors (by omega)] at this
      apply Prime.not_dvd_prod prime_two (by
        simp
        intro a x hx hk hk0 h
        rw [← h, Nat.factorization_mul hk0 hk0, Finsupp.add_apply]
        omega
      ) at this
      simp at this

  have h2 : (Finset.filter (fun i ↦ IsSquare i) (Finset.Icc 1 100)) = {1, 4, 9, 16, 25, 36, 49, 64, 81, 100} := by
    ext x
    simp
    constructor
    . intro ⟨⟨hx1, hx2⟩, ⟨k, hk⟩⟩
      have hk1 : k ≤ 10 := by nlinarith
      interval_cases x
      all_goals simp
      all_goals interval_cases k <;> omega

    . unfold IsSquare
      rintro (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
      all_goals simp
      . use 1
      . use 2
      . use 3
      . use 4
      . use 5
      . use 6
      . use 7
      . use 8
      . use 9
      . use 10

  rw [h1]
  norm_cast
  rw [hn]
  field_simp
  rw [h2]
  simp
  norm_num
