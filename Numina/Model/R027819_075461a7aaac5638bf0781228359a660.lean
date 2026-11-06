import Mathlib

theorem number_theory_16198 : {p : ℕ | p.Prime ∧ 39 ∣ p}.encard = 0 := by 
  have h1 : ∀ p : ℕ, ¬ (p.Prime ∧ 39 ∣ p) := by 
    intro p
    intro h 
    rcases h with ⟨h_prime, h_div⟩
    have h2 : p > 3 := by
      by_contra h'
      push_neg at h'
      interval_cases p <;> norm_num at h_prime h_div
      <;> try { 
        tauto 
      }
      <;> try { 
        tauto 
      }
    have h3 : p > 13 := by 
      by_contra h'
      push_neg at h'
      interval_cases p <;> norm_num at h_prime h_div 
      <;> try { 
        tauto 
      } 
      <;> try { 
        tauto 
      }
    have h5 : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals 
        omega 
      all_goals 
        omega 
    contradiction 
  have h2 : {p : ℕ | p.Prime ∧ 39 ∣ p} = ∅ := by 
    ext p
    simp [h1]
  rw [h2]
  simp