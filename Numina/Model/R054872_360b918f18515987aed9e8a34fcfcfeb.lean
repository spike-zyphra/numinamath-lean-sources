import Mathlib

theorem algebra_15190 {n : ℕ} : (8 ^ n) * (8 ^ n) * (8 ^ n) = 64 ^ 3 ↔ n = 2 := by
  constructor
  · -- Forward direction: Assume (8^n)*(8^n)*(8^n) = 64^3, prove n = 2
    intro h_eq
    have h1 : ((8 : ℕ) ^ n) * ((8 : ℕ) ^ n) * ((8 : ℕ) ^ n) = (8 : ℕ) ^ (n * 3) := by
      ring_nf
      <;> rw [←Nat.pow_mul]
      <;> ring_nf
      all_goals linarith
    rw [h1] at h_eq
    have h2 : (8 : ℕ) ^ (n * 3) = (8 : ℕ) ^ (6 : ℕ) := by
      have : (64 : ℕ) ^ 3 = 8 ^ (6 : ℕ) := by
        norm_num
      rw [this] at h_eq
      exact h_eq
    have h3 : n * 3 = 6 := by
      have h4 : (8 : ℕ) ^ (n * 3) = (8 : ℕ) ^ (6 : ℕ) := h2
      exact Nat.pow_right_injective (by norm_num) h4
    have h4 : n = 2 := by
      omega
    exact h4
  · -- Reverse direction: Assume n = 2, prove (8^n)*(8^n)*(8^n) = 64^3
    intro h_eq
    rw [h_eq]
    norm_num
    <;> ring_nf
    <;> norm_num
    all_goals linarith