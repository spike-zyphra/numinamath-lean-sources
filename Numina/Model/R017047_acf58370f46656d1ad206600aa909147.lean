import Mathlib

theorem number_theory_58310 (kate_age : ℕ) (h : ∏ i ∈ Finset.Icc 1 kate_age, i = 1307674368000) :
    kate_age = 15 := by 
  have h1 : kate_age ≤ 20 := by 
    by_contra h2 
    push_neg at h2 
    have h21 : kate_age ≥ 17 := by linarith 
    have h23 : (17 : ℕ) ∣ ∏ i ∈ Finset.Icc 1 kate_age, i := by 
      have h18 : 17 ≤ kate_age := by linarith 
      have h19 : 17 ∈ Finset.Icc (1 : ℕ) kate_age := by 
        simp at *
        all_goals omega 
      apply Finset.dvd_prod_of_mem 
      exact h19 
    have h0 : ∏ i ∈ Finset.Icc 1 kate_age, i = 1307674368000 := h 
    have h25 : (17 : ℕ) ∣ 1307674368000 := by 
      rw [← h0] 
      exact h23 
    omega 
  have h21 : kate_age ≤ 20 := h1 
  have h22 : kate_age ≥ 1 := by 
    by_contra h2 
    push_neg at h2 
    have h3 : kate_age = 0 := by linarith 
    rw [h3] at h 
    simp [Finset.prod_eq_zero] at h 
    all_goals omega 
  interval_cases kate_age <;> try { 
    simp [Finset.prod_Icc_succ_top, Finset.prod_eq_zero] at h ⊢ 
    <;> try { 
      all_goals 
        omega 
    } 
  }