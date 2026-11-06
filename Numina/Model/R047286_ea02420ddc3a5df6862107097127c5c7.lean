import Mathlib

theorem number_theory_145400 (n : ℕ) :
    if (Even n) then 2^n % 3 = 1 else 2^n % 3 = 2 := by
  by_cases h : Even n
  · -- Assume n is even
    have h4 : 2 ^ n % 3 = 1 := by 
      have h2 : ∀ (k : ℕ), (2 ^ (2 * k) : ℕ) % 3 = 1 := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          have h2 : (2 ^ (2 * (k + 1) : ℕ) : ℕ) = (2 ^ (2 * k : ℕ) : ℕ) * (2 ^ 2 : ℕ) := by 
            ring_nf
          rw [h2]
          simp [Nat.mul_mod, ih] at *
          all_goals 
            omega
      have h10 : ∃ k, n = 2 * k := by 
        obtain ⟨k, ht⟩ := h
        refine' ⟨k, by omega⟩
      rcases h10 with ⟨k, hk1⟩ 
      specialize h2 k 
      rw [show n = 2 * k by omega] 
      simpa using h2
    simp [if_pos h, h4]
  · -- Assume n is odd
    have h4 : 2 ^ n % 3 = 2 := by
      have h1 : n % 2 = 1 := by 
        have h11 : ¬Even n := h 
        by_contra h2 
        push_neg at h2
        have : Even n := by 
          refine' ⟨n / 2, by omega⟩ 
        contradiction 
      have h1' : ∀ (k : ℕ), (2 ^ (2 * k + 1) : ℕ) % 3 = 2 := by 
        intro k
        induction k with 
        | zero => 
          simp 
        | succ k ih => 
          have h3 : (2 ^ (2 * (k + 1) + 1 : ℕ) : ℕ) = (2 ^ (2 * k + 1 : ℕ) : ℕ) * (2 ^ 2 : ℕ) := by 
            ring_nf 
          rw [h3]
          simp [Nat.mul_mod, ih] at * 
          all_goals 
            omega
      have h10 : ∃ k, n = 2 * k + 1 := by 
        have h3 : n % 2 = 1 := h1
        refine ⟨(n - 1) / 2, by omega⟩ 
      rcases h10 with ⟨k, hk1⟩ 
      specialize h1' k 
      rw [show n = 2 * k + 1 by omega] 
      simpa using h1' 
    simp [if_neg h, h4]