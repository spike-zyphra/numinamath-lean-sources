import Mathlib

theorem number_theory_4955 (k : ℕ) : 7 ∣ 5^(12 * k) + 2^(6 * k + 1) - 3 := by
  have h1 : ∀ k : ℕ, (5 : ℕ) ^ (12 * k) % 7 = 1 := by
    intro k 
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h2 : (5 : ℕ) ^ (12 * (k + 1)) % 7 = 1 := by 
        have h3 : (5 : ℕ) ^ (12 * (k + 1)) = (5 ^ (12 * k)) * (5 ^ 12) := by 
          ring_nf 
        rw [h3]
        simp [Nat.mul_mod, ih] at *
        <;> norm_num 
      exact h2
  have h2 : ∀ k : ℕ, (2 : ℕ) ^ (6 * k + 1) % 7 = 2 := by
    intro k 
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h3 : (2 : ℕ) ^ (6 * (k + 1) + 1) % 7 = 2 := by
        have h3 : (2 : ℕ) ^ (6 * (k + 1) + 1) = (2 ^ (6 * k + 1)) * (2 ^ 6) := by
          ring_nf 
        rw [h3]
        simp [Nat.mul_mod, ih] at *
        <;> norm_num 
      exact h3
  have h3 : ((5 : ℕ) ^ (12 * k) + (2 : ℕ) ^ (6 * k + 1) ) % 7 = 3 := by
    have h4 : (5 : ℕ) ^ (12 * k) % 7 = 1 := h1 k 
    have h5 : (2 : ℕ) ^ (6 * k + 1) % 7 = 2 := h2 k 
    omega 
  have h4 : 7 ∣ 5 ^ (12 * k) + 2 ^ (6 * k + 1) - 3 := by
    omega 
  exact h4