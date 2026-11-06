import Mathlib

theorem number_theory_136458 :
    {a : ℕ | 0 < a ∧ a ≤ 50000 ∧ a.primeFactors.card = 2 ∧ 2 ∈ a.primeFactors ∧ 7 ∈ a.primeFactors ∧ (a.divisors.card) ∣ a}.encard = 5 ∧
    IsLeast {a | 0 < a ∧ a ≤ 50000 ∧ a.primeFactors.card = 2 ∧ 2 ∈ a.primeFactors ∧ 7 ∈ a.primeFactors ∧ (a.divisors.card) ∣ a} 56 := by
  constructor 
  · -- Show that the set of positive integers a <= 50000 with exactly two prime factors (2 and 7)
    -- and where the number of divisors divides a has cardinality 5 is the given set
    have h1 : {a : ℕ | 0 < a ∧ a ≤ 50000 ∧ a.primeFactors.card = 2 ∧ 2 ∈ a.primeFactors ∧ 7 ∈ a.primeFactors ∧ (a.divisors.card) ∣ a} = 
              Finset.filter (fun a => 0 < a ∧ a ≤ 50000 ∧ a.primeFactors.card = 2 ∧ 2 ∈ a.primeFactors ∧ 7 ∈ a.primeFactors ∧ (a.divisors.card) ∣ a) (Finset.Icc 0 50000) := by
      ext a
      simp
      <;> try { tauto }
      <;> try { omega }
    rw [h1]
    rw [Set.encard_coe_eq_coe_finsetCard]
    native_decide
  · -- Show 56 is the minimum element in the set
    constructor
    · -- Show that 56 is in the set
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · -- Show that the card of prime factors is 2
        native_decide
      constructor
      · -- Show 2 is in the prime factors
        native_decide
      constructor
      · -- Show 7 is in the prime factors
        native_decide
      · -- Show that the number of divisors divides 56
        native_decide
    · -- Show no number less than 56 is in the set
      intro a ha
      rcases ha with ⟨ha0, ha50k, hv2, h2, h7, hdiv⟩
      by_contra h
      push_neg at h
      interval_cases a <;> norm_num at *
      <;> try { contradiction }