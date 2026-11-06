import Mathlib

theorem number_theory_23011 {n : ℕ} (h₀ : n ∈ Finset.Icc 100 999) (h₁ : ∃ k, n = k * 111) (h₂ : n.primeFactors.sum id = 47) :
    n = 777 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₁ with ⟨k, rfl⟩
  rcases h₀ with ⟨h3, h4⟩
  have h5 : k ≤ 9 := by
    by_contra h
    push_neg at h 
    have h6 : k ≥ 10 := by linarith 
    have h7 : k * 111 ≥ 1110 := by 
      nlinarith
    linarith
  have h6 : k ≥ 1 := by 
    by_contra h 
    push_neg at h 
    have h7 : k = 0 := by linarith 
    have h8 : k * 111 = 0 := by 
      nlinarith [h7] 
    omega 
  interval_cases k <;> norm_num [Nat.primeFactors, Nat.primeFactorsList] at h₂ ⊢ 
  <;> try { contradiction } <;> try { trivial } 
  all_goals try { 
    have : (111 : ℕ).primeFactors.sum id = 40 := by 
      native_decide
    omega 
  }
  all_goals try { 
    have : (222 : ℕ).primeFactors.sum id = 42 := by 
      native_decide 
    omega 
  }
  all_goals try { 
    have : (333 : ℕ).primeFactors.sum id = 40 := by 
      native_decide 
    omega 
  }
  all_goals try { 
    have : (444 : ℕ).primeFactors.sum id = 42 := by 
      native_decide 
    omega 
  }
  all_goals try { 
    have : (555 : ℕ).primeFactors.sum id = 45 := by 
      native_decide 
    omega 
  }
  all_goals try { 
    have : (666 : ℕ).primeFactors.sum id = 42 := by 
      native_decide 
    omega 
  }
  all_goals try { 
    have : (888 : ℕ).primeFactors.sum id = 42 := by 
      native_decide 
    omega 
  }
  all_goals try { 
    have : (999 : ℕ).primeFactors.sum id = 40 := by 
      native_decide 
    omega 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    native_decide 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    nlinarith 
  }
  <;> try { contradiction }
  <;> try { trivial }
  <;> try { nlinarith } 
  <;> try { tauto }
  <;> try { contradiction }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }