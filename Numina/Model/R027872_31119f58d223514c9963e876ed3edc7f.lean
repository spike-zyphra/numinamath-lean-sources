import Mathlib

theorem number_theory_321903 (n : ℕ) (hn : 0 < n) :
    3 ∣ (2 ^ n * n + 1) ↔ n % 6 = 1 ∨ n % 6 = 2 := by
  constructor
  · -- Assume 3 ∣ (2 ^ n * n + 1), need to prove n % 6 = 1 ∨ n % 6 = 2
    intro h
    have h1 : (2 ^ n * n + 1) % 3 = 0 := by
      omega
    have h3 : ∀ n : ℕ, (2 ^ n) % 3 = 1 ∨ (2 ^ n) % 3 = 2 := by
      intro n
      induction n with
      | zero => 
        simp
      | succ n ih => 
        simp [Nat.pow_add, Nat.mul_mod] at ih ⊢
        omega
    have h4 : (2 ^ n) % 3 = 1 ∨ (2 ^ n) % 3 = 2 := h3 n
    have h7 : (2 ^ n * n) % 3 = 2 := by
      omega
    rcases h4 with (h8 | h8)
    · -- Case where 2^n % 3 = 1
      have h9 : n % 3 = 2 := by
        simp [Nat.mul_mod, h8] at h7
        omega
      have h10 : n % 2 = 0 := by
        by_contra h
        push_neg at h
        have h11 : n % 2 = 1 := by omega
        have h12 : (2 ^ n) % 3 = 2 := by
          have h13 : ∀ k : ℕ, (2 ^ (2 * k + 1)) % 3 = 2 := by
            intro k
            induction k with
            | zero => simp
            | succ k ih => 
              simp [pow_add, pow_mul] at ih ⊢
              omega
          have h14 : ∃ k, n = 2 * k + 1 := by
            refine' ⟨(n - 1) / 2, by omega⟩
          rcases h14 with ⟨k, hk⟩
          rw [hk]
          exact h13 k
        omega
      have h11 : n % 6 = 2 := by
        omega
      right
      omega
    · -- Case where 2^n % 3 = 2
      have h9 : n % 3 = 1 := by
        simp [Nat.mul_mod, h8] at h7
        omega
      have h10 : n % 2 = 1 := by
        by_contra h
        push_neg at h
        have h11 : n % 2 = 0 := by omega
        have h12 : (2 ^ n) % 3 = 1 := by
          have h13 : ∀ k : ℕ, (2 ^ (2 * k)) % 3 = 1 := by
            intro k
            induction k with
            | zero => simp
            | succ k ih => 
              simp [pow_add, pow_mul] at ih ⊢
              omega
          have h14 : ∃ k, n = 2 * k := by
            refine' ⟨n / 2, by omega⟩
          rcases h14 with ⟨k, hk⟩
          rw [show n = 2 * k by omega]
          exact h13 k
        omega
      have h11 : n % 6 = 1 := by
        omega
      left
      omega
  · -- Assume n % 6 = 1 ∨ n % 6 = 2, prove 3 ∣ (2 ^ n * n + 1)
    intro h
    rcases h with (h | h)
    · -- Case where n % 6 = 1
      have h1 : n % 6 = 1 := h
      have h2 : n % 2 = 1 := by
        omega
      have h3 : (2 ^ n) % 3 = 2 := by
        have h14 : ∀ k : ℕ, (2 ^ (2 * k + 1)) % 3 = 2 := by
          intro k
          induction k with
          | zero => simp
          | succ k ih => 
            simp [pow_add, pow_mul] at ih ⊢
            omega
        have h15 : ∃ k, n = 2 * k + 1 := by
          refine' ⟨(n - 1) / 2, by omega⟩
        rcases h15 with ⟨k, hk⟩
        rw [hk]
        exact h14 k
      have h5 : n % 3 = 1 := by
        omega
      have h1 : (2 ^ n * n + 1) % 3 = 0 := by
        simp [Nat.add_mod, Nat.mul_mod, h3, h5]
      omega
    · -- Case where n % 6 = 2
      have h1 : n % 6 = 2 := h
      have h2 : n % 2 = 0 := by
        omega
      have h4 : (2 ^ n) % 3 = 1 := by
        have h13 : ∀ k : ℕ, (2 ^ (2 * k)) % 3 = 1 := by
          intro k
          induction k with
          | zero => simp
          | succ k ih => 
            simp [pow_add, pow_mul] at ih ⊢
            omega
        have h14 : ∃ k, n = 2 * k := by
          refine' ⟨n / 2, by omega⟩
        rcases h14 with ⟨k, hk⟩
        rw [show n = 2 * k by omega]
        exact h13 k
      have h5 : n % 3 = 2 := by
        omega
      have h1 : (2 ^ n * n + 1) % 3 = 0 := by
        simp [Nat.add_mod, Nat.mul_mod, h4, h5]
      omega