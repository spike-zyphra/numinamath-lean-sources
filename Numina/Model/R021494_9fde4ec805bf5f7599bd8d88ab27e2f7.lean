import Mathlib

theorem number_theory_161478 : (∀ n : ℕ, 9 ∣ (n^3 + (n+1)^3 + (n+2)^3)) ∧
    (∀ p : ℕ, 5 ∣ p^5 - p) ∧ (∀ k : ℕ, 3 ∣ k^3 + 5 * k) := by
  constructor
  · -- Prove that for any natural n, 9 divides n³ + (n+1)³ + (n+2)³
    intro n 
    have h1 : ∀ n : ℕ, 9 ∣ (n^3 + (n + 1)^3 + (n + 2)^3) := by 
      intro n 
      induction n with 
      | zero => 
        norm_num 
      | succ n ih => 
        have h3 : 9 ∣ ((n + 1) ^ 3 + (n + 2) ^ 3 + (n + 3) ^ 3) := by 
          have h4 : 9 ∣ (n^3 + (n + 1)^3 + (n + 2)^3) := ih 
          have h5 : (n + 1) ^ 3 + (n + 2) ^ 3 + (n + 3) ^ 3 = (n^3 + (n + 1)^3 + (n + 2)^3 ) + 9 * (n ^2 + 3 * n + 3) := by
            ring_nf 
          rw [h5] 
          omega 
        simpa using h3 
    exact h1 n 
  constructor 
  · -- Prove b: ∀ p : ℕ, 5 ∣ p^5 - p 
    intro p 
    have h2 : p ^ 5 % 5 = p % 5 := by 
      have h3 : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
        omega 
      rcases h3 with (h3 | h3 | h3 | h3 | h3)
      · -- case p = 0 
        simp [h3, pow_succ, Nat.mul_mod] 
      · -- case p = 1 
        simp [h3, pow_succ, Nat.mul_mod] 
      · -- case p = 2 
        simp [h3, pow_succ, Nat.mul_mod] 
      · -- case p = 3 
        simp [h3, pow_succ, Nat.mul_mod] 
      · -- case p = 4 
        simp [h3, pow_succ, Nat.mul_mod] 
    have h4 : (p ^ 5 - p) % 5 = 0 := by 
      have h5 : p ^ 5 % 5 = p % 5 := h2 
      omega 
    omega 
  · -- Prove c: ∀ k : ℕ, 3 ∣ k^3 + 5 * k
    intro k 
    have h6 : k ^ 3 % 3 = k % 3 := by 
      have h7 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by 
        omega 
      rcases h7 with (h7 | h7 | h7)
      · -- k ≡ 0 
        simp [h7, pow_succ, Nat.mul_mod] 
      · -- k ≡ 1 
        simp [h7, pow_succ, Nat.mul_mod] 
      · -- k ≡ 2 
        simp [h7, pow_succ, Nat.mul_mod] 
    have h7 : (k ^ 3 + 5 * k) % 3 = 0 := by 
      have h8 : k ^ 3 % 3 = k % 3 := h6 
      omega 
    omega