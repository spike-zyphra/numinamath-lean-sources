import Mathlib

theorem number_theory_187878 (n : ℕ) :
    n > 0 ∧ Nat.totient n = 2002^2 - 1 ↔ False := by 
  constructor
  · -- Assume n > 0 ∧ Nat.totient n = 2002^2 - 1, prove False
    intro h
    rcases h with ⟨h₁, heq⟩
    have h3 : n > 0 := h₁
    by_cases h3 : n > 2
    · -- Assume n > 2
      have h4 : Even (Nat.totient n) := by 
        have h5 : n > 2 := h3 
        have h6 : n ≥ 3 := by omega 
        have h7 : Even (Nat.totient n) := by 
          apply Nat.totient_even 
          all_goals omega 
        exact h7
      have h8 : ¬ Even (Nat.totient n) := by 
        rw [heq] 
        norm_num [Nat.even_iff]
      contradiction
    · -- Assume n ≤ 2
      have h4 : n ≤ 2 := by omega 
      have h6 : n = 1 ∨ n = 2 := by 
        interval_cases n <;> omega 
      rcases h6 with (r | r)
      · -- n = 1
        have h7 : n = 1 := r 
        rw [h7] at heq 
        have h8 : Nat.totient 1 = 1 := by 
          simp [Nat.totient_one]
        rw [h8] at heq 
        all_goals norm_num at heq 
      · -- n = 2
        have h7 : n = 2 := r 
        rw [h7] at heq 
        have h8 : Nat.totient 2 = 1 := by 
          native_decide 
        rw [h8] at heq 
        all_goals norm_num at heq 
  · -- Assume False, prove n > 0 ∧ Nat.totient n = 2002^2 - 1
    intro h
    cases h