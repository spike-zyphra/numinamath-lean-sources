import Mathlib

theorem number_theory_160057 (k : ℕ) :
    (1 ≤ k ∧ ∃ n m : ℤ, 9 * n^6 = 2^k + 5 * m^2 + 2) ↔ k = 1 := by
  constructor
  · -- Assume 1 ≤ k ∧ ∃ n m : ℤ, 9 * n^6 = 2^k + 5 * m^2 + 2, prove k = 1
    intro h
    rcases h with ⟨hk1, ⟨n, m, heq⟩⟩
    by_cases h2 : k = 1
    · -- k = 1
      omega
    · -- k ≠ 1
      have h2' : k ≥ 2 := by
        by_contra h
        push_neg at h
        have : k = 1 := by linarith
        tauto
      have eq1 := heq
      have : (9 * n^6 : ℤ) % 4 = (2^k + 5 * m^2 + 2 : ℤ) % 4 := by
        omega
      have h3 : (9 * n^6 : ℤ) % 4 = (n ^ 6) % 4 := by
        omega
      rw [h3] at this
      -- Now, compute right side
      have h4 : (2^k + 5 * m^2 + 2 : ℤ) % 4 = (m ^ 2 + 2) % 4 := by
        have h5 : k ≥ 2 := h2'
        have h3 : (2 : ℤ) ^ k % 4 = 0 := by
          have h2k : ∀ (k : ℕ), k ≥ 2 → (2 : ℤ) ^ k % 4 = 0 := by
            intro k hk
            induction k with
            | zero => 
              omega
            | succ k ih => 
              cases k with
              | zero => 
                omega
              | succ k => 
                simp [pow_add, pow_one, Int.add_emod, Int.mul_emod] at ih ⊢
                all_goals omega
          specialize h2k k (by omega)
          simpa using h2k
        have h5m : (5 * m ^ 2 : ℤ) % 4 = (m ^ 2 : ℤ) % 4 := by
          omega
        omega
      rw [h4] at this
      -- Now proving contradiction
      have h5 : n ^ 6 % 4 = 0 ∨ n ^ 6 % 4 = 1 := by
        have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
          omega
        rcases h1 with (h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      have h6 : (m ^ 2 : ℤ) % 4 = 0 ∨ (m ^ 2 : ℤ) % 4 = 1 := by
        have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
          omega
        rcases h1 with (h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      have h7 : (m ^ 2 + 2) % 4 = 2 ∨ (m ^ 2 + 2) % 4 = 3 := by
        rcases h6 with (h6 | h6)
        · 
          omega
        · 
          omega
      omega
  · -- Assume k = 1, prove 1 ≤ k ∧ ∃ n m : ℤ, 9 * n^6 = 2^k + 5 * m^2 + 2
    intro h
    rw [h]
    constructor
    · -- 1 ≤ 1
      omega
    · -- ∃ n m : ℤ, 9 * n^6 = 2^1 + 5 * m^2 + 2
      use 1, 1
      norm_num