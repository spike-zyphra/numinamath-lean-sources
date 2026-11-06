import Mathlib

/-The number of triangles with side lengths being the prime factors of 1995 is 13-/
theorem my_favorite_theorem :
  {(p, q, r) : ℕ × ℕ × ℕ | p.Prime ∧ q.Prime ∧ r.Prime ∧
  p ≤ q ∧ q ≤ r ∧ p + q > r ∧
  p ∣ 1995 ∧ q ∣ 1995 ∧ r ∣ 1995}.ncard = 13 := by
  -- Define the explicit set of all valid triples
  let S0:Finset (ℕ × ℕ × ℕ):={(3,3,3),(5,5,5),(7,7,7),(19,19,19),(3,3,5),(3,5,5),(5,5,7),(3,7,7),
    (5,7,7),(3,19,19),(5,19,19),(7,19,19),(3,5,7)}

  -- Prove that the condition set equals our explicit set S0
  have h:{(p, q, r) : ℕ × ℕ × ℕ | p.Prime ∧ q.Prime ∧ r.Prime ∧
    p ≤ q ∧ q ≤ r ∧ p + q > r ∧
    p ∣ 1995 ∧ q ∣ 1995 ∧ r ∣ 1995}
    = S0 := by
    ext ⟨p, q, r⟩
    constructor

    -- Forward direction: if (p,q,r) satisfies conditions, then it's in S0
    · intro ⟨hp_prime, hq_prime, hr_prime, hpq, hqr, hpqr, hp_div, hq_div, hr_div⟩
      -- Prime factorization of 1995 is {3, 5, 7, 19}
      have h1995 : Nat.primeFactors 1995= {3,5,7,19} := by native_decide

      -- Each prime must be a factor of 1995
      have hp_in:p∈Nat.primeFactors 1995:=(Nat.mem_primeFactors_of_ne_zero (by norm_num)).mpr (by tauto)
      have hq_in:q∈Nat.primeFactors 1995:=(Nat.mem_primeFactors_of_ne_zero (by norm_num)).mpr (by tauto)
      have hr_in:r∈Nat.primeFactors 1995:=(Nat.mem_primeFactors_of_ne_zero (by norm_num)).mpr (by tauto)

      -- Substitute the known prime factors
      rw[h1995] at hp_in hq_in hr_in
      simp

      -- Case analysis on all possible combinations of primes
      fin_cases hp_in
      all_goals
        fin_cases hq_in
        all_goals
          fin_cases hr_in
          all_goals
            simp only [S0]
            try omega
            try decide

    -- Backward direction: if (p,q,r) is in S0, then it satisfies all conditions
    · intro h_in_S0
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_in_S0
      simp at h_in_S0

      -- Verify each element of S0 satisfies the conditions
      fin_cases h_in_S0
      all_goals
        constructor
        · norm_num
        · norm_num

  -- Use the equality to compute the cardinality
  rw[h]
  rw [Set.ncard_coe_Finset]
  decide
