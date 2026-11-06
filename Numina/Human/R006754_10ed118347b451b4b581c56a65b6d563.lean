import Mathlib

open Nat Finset

theorem number_theory_640815 {n0 : ℕ} (hn0 : Squarefree n0) (npos : n0 > 0) (hn01 : n0 ≠ 1) (a : ℕ) (ha : a > 0) (k : ℕ) (hk : k = n0.primeFactors.card) :
  ((n0 ^ a).divisors \ {1, n0 ^ a}).card = (a + 1)^k - 2 := by 
  unfold Squarefree at hn0
  have h1 : ∀ p ∈ n0.primeFactors, n0.factorization p = 1 := by 
    intro p hp
    simp at hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    have aux_ge : n0.factorization p ≥ 1 := by 
      exact (Prime.dvd_iff_one_le_factorization hp1 hp3).mp hp2
    have aux_le : n0.factorization p ≤ 1 := by 
      by_contra hc
      simp at hc
      have psq_dvd : p ^ 2 ∣ n0 := by 
        exact (Prime.pow_dvd_iff_le_factorization hp1 hp3).mpr hc
      obtain hp4 := hn0 p
      rw [←show p ^ 2 = p * p by ring] at hp4
      obtain hp5 := hp4 psq_dvd
      have nunit : ¬ IsUnit p := by 
        exact hp1.not_unit
      exact nunit hp5
    linarith
  have set_eq : ((n0 ^ a).divisors \ {1, n0 ^ a}) = 
    (((n0 ^ a).divisors.erase 1).erase (n0^ a)) := by 
    refine Finset.ext_iff.mpr ?_
    intro x
    constructor
    · intro hx
      simp at hx ⊢ 
      obtain ⟨hx1, hx3, hx4⟩ := hx
      obtain ⟨hx1, hx2⟩ := hx1
      exact ⟨hx4, hx3, hx1, hx2⟩
    · simp
      intro hx1 hx2 hx3 hx4
      constructor
      exact ⟨hx3, hx4⟩
      exact ⟨hx2, hx1⟩
  have card_eq : ((n0 ^ a).divisors \ {1, n0 ^ a}).card = 
    ((n0 ^ a).divisors.erase 1).card - 1 := by 
    rw [set_eq]
    refine Finset.card_erase_of_mem ?_
    simp
    constructor
    · have aux1 : n0 ^ a > 1 := by 
        refine Nat.one_lt_pow ?_ ?_
        linarith
        omega
      linarith
    · intro hc
      linarith
  have card_eq2 : ((n0 ^ a).divisors.erase 1).card = ((n0 ^ a).divisors).card - 1 := by 
    refine Finset.card_erase_of_mem ?_
    simp
    intro hc
    linarith
  rw [card_eq, card_eq2]
  have eq1 : (n0 ^ a).divisors.card = (a + 1) ^ k := by 
    rw [Nat.card_divisors, factorization_pow]
    have aux : ∏ x ∈ (n0 ^ a).primeFactors, ((a • n0.factorization) x + 1) = 
      ∏ x ∈ (n0 ^ a).primeFactors, (a + 1) := by 
      apply Finset.prod_congr (by rfl)
      intro x hx
      simp at hx
      obtain ⟨hx1, hx2, hx3⟩ := hx
      have aux2 : x ∈ n0.primeFactors := by 
        refine mem_primeFactors.mpr ?_
        constructor
        · exact hx1
        constructor
        · exact Nat.Prime.dvd_of_dvd_pow hx1 hx2
        · linarith
      simp [h1 x aux2]
    rw [aux]
    have aux3 : (n0 ^ a).primeFactors = n0.primeFactors := by 
      refine primeFactors_pow n0 ?_
      linarith
    rw [aux3, prod_const, ←hk]
    positivity
  rw [eq1]
  omega