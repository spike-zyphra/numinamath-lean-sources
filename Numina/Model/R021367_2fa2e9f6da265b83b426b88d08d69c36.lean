import Mathlib


theorem number_theory_116405 : 2023^(2024^2025) % 10 = 1 := by 
  have h1 : 2023 % 10 = 3 := by norm_num
  have h2 : (2024 ^ 2025) % 4 = 0 := by
    omega
  have h3 : (2023 ^ (2024 ^ 2025 : ℕ)) % 10 = 1 := by 
    have h4 : ∀ k : ℕ, (2023 ^ (4 * k : ℕ)) % 10 = 1 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
        all_goals omega
    have h5 : (2024 ^ 2025 : ℕ) % 4 = 0 := h2
    have h6 : ∃ k : ℕ, (2024 ^ 2025 : ℕ) = 4 * k := by 
      refine' ⟨(2024 ^ 2025) / 4, by omega⟩
    rcases h6 with ⟨k, hk⟩
    rw [show (2023 ^ (2024 ^ 2025 : ℕ)) = (2023 ^ (4 * k : ℕ)) by rw [hk]]
    apply h4 k 
  exact h3