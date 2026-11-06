import Mathlib

theorem number_theory_7331 (n : ℕ) (hn : n > 0) : 30 ∣ n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) := by
  have h1 : n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) % 5 = 0 := by
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4)
    · -- n % 5 = 0
      have h8 : n % 5 = 0 := by omega
      have h9 : n % 5 = 0 := h8 
      have h3 : (n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1)) % 5 = 0 := by 
        simp [Nat.mul_mod, h9]
      omega
    · -- n % 5 = 1
      have h8 : n % 5 = 1 := by omega
      have hk1 : ∃ k, n = 5 * k + 1 := by 
        have h6 : n % 5 = 1 := h8
        have : n = 5 * (n / 5) + 1 := by omega
        exact ⟨n / 5, this⟩
      rcases hk1 with ⟨k, hk⟩
      have h9 : (3 * n ^ 2 + 3 * n - 1) % 5 = 0 := by 
        rw [show n = 5 * k + 1 by omega]
        ring_nf
        <;> omega 
      have h3 : (n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1)) % 5 = 0 := by 
        simp [Nat.mul_mod, h9]
      omega
    · -- n % 5 = 2
      have h8 : n % 5 = 2 := by omega
      have hk2 : ∃ k, n = 5 * k + 2 := by 
        have h6 : n % 5 = 2 := h8
        have : n = 5 * (n / 5) + 2 := by omega
        exact ⟨n / 5, this⟩
      rcases hk2 with ⟨k, hk⟩
      have h9 : (2 * n + 1) % 5 = 0 := by 
        rw [show n = 5 * k + 2 by omega]
        all_goals ring_nf <;> omega 
      have h3 : (n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1)) % 5 = 0 := by 
        simp [Nat.mul_mod, h9]
      omega
    · -- n % 5 = 3
      have h8 : n % 5 = 3 := by omega
      have hk3 : ∃ k, n = 5 * k + 3 := by 
        have h6 : n % 5 = 3 := h8
        have : n = 5 * (n / 5) + 3 := by omega
        exact ⟨n / 5, this⟩
      rcases hk3 with ⟨k, hk⟩
      have h9 : (3 * n ^ 2 + 3 * n - 1) % 5 = 0 := by 
        rw [show n = 5 * k + 3 by omega]
        ring_nf
        <;> omega 
      have h3 : (n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1)) % 5 = 0 := by 
        simp [Nat.mul_mod, h9]
      omega
    · -- n % 5 = 4
      have h8 : n % 5 = 4 := by omega
      have hk4 : ∃ k, n = 5 * k + 4 := by 
        have h6 : n % 5 = 4 := h8
        have : n = 5 * (n / 5) + 4 := by omega
        exact ⟨n / 5, this⟩
      rcases hk4 with ⟨k, hk⟩
      have h9 : (n + 1) % 5 = 0 := by 
        rw [show n = 5 * k + 4 by omega]
        all_goals ring_nf <;> omega 
      have h3 : (n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1)) % 5 = 0 := by 
        simp [Nat.mul_mod, h9]
      omega
  -- Check divisibility by 2, 3 as well
  have h2 : n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) % 2 = 0 := by
    have h4 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h4 with (h4 | h4)
    · -- n is even
      simp [Nat.mul_mod, h4, Nat.add_mod, Nat.mul_mod]
      all_goals omega
    · -- n is odd
      simp [Nat.mul_mod, h4, Nat.add_mod, Nat.mul_mod]
      all_goals omega
  have h3 : n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) % 3 = 0 := by
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h4 with (h4 | h4 | h4)
    · -- n % 3 = 0
      simp [Nat.mul_mod, h4, Nat.add_mod, Nat.mul_mod]
      all_goals omega
    · -- n % 3 = 1
      simp [Nat.mul_mod, h4, Nat.add_mod, Nat.mul_mod]
      all_goals omega
    · -- n % 3 = 2
      simp [Nat.mul_mod, h4, Nat.add_mod, Nat.mul_mod]
      all_goals omega
  omega