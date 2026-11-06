import Mathlib

theorem number_theory_14957 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : Even n) (h₂ : 11 ∣ n) (h₃ : ∃ k, k^3 = (Nat.digits 10 n).prod) :
    n = 88 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> norm_num [Nat.even_iff] at h₁ h₂ h₄ h₅ ⊢ 
    <;> try { 
      rcases h₃ with ⟨k, hk⟩ 
      norm_num at hk 
      have : k ≤ 4 := by 
        by_contra h 
        push_neg at h 
        have h8 : k ≥ 5 := by linarith 
        have : k^3 ≥ 125 := by 
          have h9 : k ≥ 5 := by linarith 
          have h10 : k ^ 3 ≥ 5 ^ 3 := by apply Nat.pow_le_pow_of_le_left h9 3 
          norm_num at h10 ⊢ 
          linarith 
        have h11 : k^3 ≤ 64 := by 
          omega 
        omega 
      interval_cases k <;> omega 
    } <;> omega