import Mathlib

theorem number_theory_206343 (n : ℕ) :
    ∃ s : Finset ℕ, s.card = n ∧
      (∀ i ∈ s, i > 0) ∧
      (∑ i ∈ s, i^3) = (∑ i ∈ s, i) ^ 2 := by

  use (Finset.Icc 1 n)
  constructor 
  · -- Show that the cardinality of the set is n 
    simp
  constructor
  · -- Show that all elements in the set are > 0
    intro i hi 
    have h1 : i ≥ 1 := by 
      have h2 : i ∈ Finset.Icc 1 n := by 
        simpa using hi
      simp at h2 ⊢ 
      omega
    linarith
  · -- Show that the sum of the cubes is equal to the square of the sum 
    have h2 : ∀ m : ℕ, (∑ i in Finset.Icc 1 m, i^3) = (∑ i in Finset.Icc 1 m, i) ^ 2 := by 
      intro m 
      induction m with 
      | zero => 
        simp 
      | succ m ih =>
        rw [Finset.sum_Icc_succ_top (by linarith), Finset.sum_Icc_succ_top (by linarith)]
        rw [ih]
        have eq2 : (∑ i in Finset.Icc 1 m, i) ^ 2 + (m + 1) ^ 3 = (∑ i in Finset.Icc 1 m, i + (m + 1)) ^ 2 := by 
          have eq3 : (∑ i in Finset.Icc 1 m, i + (m + 1)) ^ 2 = (∑ i in Finset.Icc 1 m, i) ^ 2 + 2 * (∑ i in Finset.Icc 1 m, i) * (m + 1) + (m + 1) ^ 2 := by 
            ring 
          have eq4 : (∑ i in Finset.Icc 1 m, i : ℕ) ^ 2 + (m + 1) ^ 3 = (∑ i in Finset.Icc 1 m, i : ℕ) ^ 2 + 2 * (∑ i in Finset.Icc 1 m, i : ℕ) * (m + 1) + (m + 1) ^ 2 := by 
            have h3 : (∑ i in Finset.Icc 1 m, i : ℕ) * 2 = m * (m + 1) := by 
              have h4 : ∀ (m : ℕ), (∑ i in Finset.Icc 1 m, i : ℕ) * 2 = m * (m + 1) := by 
                intro m 
                induction m with 
                | zero => 
                  simp 
                | succ m ih =>
                  rw [Finset.sum_Icc_succ_top (by linarith)]
                  simp [add_mul, mul_add] at ih ⊢
                  all_goals 
                    cases m with 
                    | zero => 
                      all_goals simp at ih ⊢ <;> omega 
                    | succ m => 
                      simp [mul_add, add_mul] at ih ⊢ 
                      all_goals 
                        ring_nf at ih ⊢
                        all_goals 
                          omega 
              specialize h4 m 
              simpa using h4 
            nlinarith [h3, sq_nonneg ((∑ i in Finset.Icc 1 m, i : ℕ) : ℕ), sq_nonneg ((m + 1) : ℕ)]
          linarith [eq3, eq4]
        linarith [eq2]
    specialize h2 n 
    simpa using h2