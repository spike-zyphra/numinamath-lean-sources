import Mathlib

theorem number_theory_232820 :
    ∃ s1 s2 s3 s4 : Finset ℕ,
      s1 = {1, 2, 3} ∧
      s2 = {0, 3, 6} ∧
      s3 = {0, 9, 18} ∧
      s4 = {0, 27, 54} ∧
      ∀ n ∈ Finset.Icc 1 81, ∃ a ∈ s1, ∃ b ∈ s2, ∃ c ∈ s3, ∃ d ∈ s4,
        n = a + b + c + d := by 
  refine' ⟨{1, 2, 3}, {0, 3, 6}, {0, 9, 18}, {0, 27, 54}, rfl, rfl, rfl, rfl, ?_⟩
  intro n hn
  have h1 : n ≥ 1 := by
    simp at hn
    omega
  have h2 : n ≤ 81 := by
    simp at hn
    omega
  interval_cases n <;> try { 
    native_decide
  }
  <;> try { 
    native_decide
  }
  <;> try { 
    native_decide
  }
  <;> try { 
    native_decide
  }
  <;> try { 
    native_decide
  }
  <;> try { 
    native_decide
  }
  all_goals 
    native_decide