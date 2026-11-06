import Mathlib

theorem number_theory_12381 : Set.ncard {n : ℕ | n < 10000 ∧ IsSquare n ∧
    ∃ k, n = (k + 1) ^ 2 - k ^ 2} = 50 := by
  have h_eq : {n : ℕ | n < 10000 ∧ IsSquare n ∧ 
      ∃ k, n = (k + 1) ^ 2 - k ^ 2} = 
      Finset.filter (fun n => IsSquare n ∧ (n % 2 = 1)) (Finset.Iio 10000) := by
    ext n 
    simp
    intro h1 h2
    have h7 : (∃ k, n = (k + 1) ^ 2 - k ^ 2) ↔ n % 2 = 1 := by
      constructor
      · -- ( (k : ℕ ), n = (k + 1) ^ 2 - k ^ 2 ) 
        intro h 
        rcases h with ⟨k, hk⟩
        have h5 : (k + 1 : ℕ) ^ 2 - k ^ 2 = 2 * k + 1 := by
          have h6 : (k + 1 : ℕ) ^ 2 = k ^ 2 + 2 * k + 1 := by 
            ring_nf
          omega
        have h5_eq : n = 2 * k + 1 := by 
          omega 
        omega 
      · -- intro h 
        intro h 
        have h7 : n % 2 = 1 := by 
          omega
        have h54 : ∃ k, n = (k + 1) ^ 2 - k ^ 2 := by
          have h8 : n % 2 = 1 := h7
          have h9 : n % 2 = 1 := h8
          have h10 : n = 2 * ((n - 1) / 2) + 1 := by omega
          refine ⟨(n - 1) / 2, ?_⟩ 
          have h_eq1 : ((n - 1) / 2 + 1 : ℕ) ^ 2 - ((n - 1) / 2 : ℕ) ^ 2 = 2 * ((n - 1) / 2) + 1 := by
            have eq1 : ((n - 1) / 2 + 1 : ℕ) ^ 2 = ((n - 1) / 2 : ℕ) ^ 2 + 2 * ((n - 1) / 2 : ℕ) + 1 := by
              ring_nf 
            omega 
          omega 
        tauto 
    simp [h7] 
  rw [h_eq]
  rw [Set.ncard_coe_Finset]
  native_decide