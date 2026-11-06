import Mathlib

theorem number_theory_46069 (n : ℕ) (h : 2 ≤ n) : (2^(2^n) + 1) % 10 = 7 := by
  have h1 : ∀ m : ℕ, m ≥ 1 → (m : ℕ) % 4 = 0 → (2 ^ m) % 10 = 6 := by 
    intro m hm1 hm4
    have h2 : ∀ (k : ℕ), (2 ^ (4 * (k + 1))) % 10 = 6 := by
      intro k 
      induction k with
      | zero => 
        norm_num 
      | succ k ih =>
        simp [pow_succ, pow_mul] at ih ⊢
        all_goals 
          omega
    have h3 : m = 4 * (m / 4) := by
      omega
    have h4 : m / 4 ≥ 1 := by 
      omega
    have h5 : (2 ^ (4 * (m / 4))) % 10 = 6 := by
      specialize h2 (m / 4 - 1)
      have h6 : m / 4 - 1 + 1 = m / 4 := by
        omega
      rw [h6] at h2 
      all_goals 
        try simp at h2 ⊢ <;> omega 
      all_goals omega
    rw [h3] 
    exact h5 
  have h2 : ∀ n : ℕ, n ≥ 2 → (2^n : ℕ) % 4 = 0 := by
    intro n hn 
    have h3 : n ≥ 2 := hn
    have h4 : 2^n % 4 = 0 := by
      have h5 : ∀ (k : ℕ), 2 ^ (k + 2) % 4 = 0 := by
        intro k 
        induction k with 
        | zero => 
          norm_num 
        | succ k ih => 
          simp [pow_succ] at ih ⊢
          all_goals omega
      specialize h5 (n - 2)
      have h6 : n - 2 + 2 = n := by omega
      rw [h6] at h5 
      exact h5 
    exact h4 
  have h3 : (2 ^ (2^n)) % 10 = 6 := by
    have h2' : (2^n : ℕ) % 4 = 0 := h2 n h
    have h4 : (2^n : ℕ) ≥ 1 := by
      have h5 : n ≥ 2 := h
      have h6 : 2^n ≥ 2^2 := by 
        apply Nat.pow_le_pow_of_le_right 
        norm_num 
        omega
      have h7 : 2^2 = 4 := by norm_num 
      linarith [h7, h6]
    have h5 : (2 ^ (2^n)) % 10 = 6 := by 
      apply h1 (2^n) h4 h2'
    exact h5 
  omega