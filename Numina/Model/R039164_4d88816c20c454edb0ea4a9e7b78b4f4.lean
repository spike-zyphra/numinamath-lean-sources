import Mathlib

theorem number_theory_154952 (n : ℕ) (hn : Odd n) :
    1975 ∣ 23 * 52 ^ n + 102 * 27 ^ n := by 
  have h3 : (23 * 52 ^ n + 102 * 27 ^ n) % 25 = 0 := by
    have h4 : ∀ (n : ℕ), (23 * 52 ^ n + 102 * 27 ^ n) % 25 = 0 := by
      intro n 
      induction n with 
      | zero => 
        norm_num 
      | succ n ih => 
        simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul] at ih ⊢ 
        all_goals omega 
    specialize h4 n
    simpa using h4
  have h4 : (23 * 52 ^ n + 102 * 27 ^ n) % 79 = 0 := by
    have h2 : n % 2 = 1 := by 
      obtain ⟨k, hk⟩ := hn 
      omega 
    have h4' : (23 * 52 ^ n + 102 * 27 ^ n) % 79 = 0 := by
      have h6 : ∃ k : ℕ, n = 2 * k + 1 := by
        have h9 : n % 2 = 1 := h2
        have h10 : n ≥ 1 := by
          by_contra h
          push_neg at h
          have : n = 0 := by linarith 
          rw [this] at h9
          omega 
        use (n - 1) / 2 
        omega 
      rcases h6 with ⟨k, hk⟩ 
      have h5 : ∀ (k : ℕ), (23 * 52 ^ (2 * k + 1) + 102 * 27 ^ (2 * k + 1)) % 79 = 0 := by
        intro k 
        induction k with 
        | zero => 
          norm_num 
        | succ k ih => 
          simp [Nat.pow_succ, Nat.pow_mul, Nat.mul_add, Nat.add_mul] at ih ⊢ 
          all_goals omega 
      rw [hk] 
      exact h5 k
    exact h4'
  omega