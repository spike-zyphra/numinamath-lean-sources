import Mathlib


theorem number_theory_284581 (n : ℕ) :
    1959 ∣ 5^(8*n) - 2^(4*n) * 7^(2*n) := by
  have h4 : ∀ n : ℕ, (5 ^ (8 * n) : ℕ) % 1959 = (2 ^ (4 * n) * 7 ^ (2 * n)) % 1959 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h2 : (5 ^ (8 * (n + 1)) : ℕ) % 1959 = (5 ^ (8 * n) * 390625) % 1959 := by
        ring_nf
      have h3 : (2 ^ (4 * (n + 1)) * 7 ^ (2 * (n + 1)) : ℕ) % 1959 = ( (2 ^ (4 * n) * 7 ^ (2 * n)) * 784 ) % 1959 := by
        ring_nf
      rw [h2, h3]
      have h5 : (5 ^ (8 * n) * 390625) % 1959 = ( (2 ^ (4 * n) * 7 ^ (2 * n)) * 784 ) % 1959 := by
        have h3 : (5 ^ (8 * n) : ℕ) % 1959 = (2 ^ (4 * n) * 7 ^ (2 * n)) % 1959 := by
          exact ih
        have h51 : (5 ^ (8 * n) * 390625) % 1959 = (2 ^ (4 * n) * 7 ^ (2 * n) * 390625) % 1959 := by
          have h7 : (5 ^ (8 * n)) % 1959 = (2 ^ (4 * n) * 7 ^ (2 * n)) % 1959 := h3
          have h8 : ( (5 ^ (8 * n)) * 390625 ) % 1959 = ( (2 ^ (4 * n) * 7 ^ (2 * n)) * 390625 ) % 1959 := by
            simp [Nat.mul_mod, h7]
          exact h8
        have h52 : (2 ^ (4 * n) * 7 ^ (2 * n) * 390625) % 1959 = ( (2 ^ (4 * n) * 7 ^ (2 * n)) * 784 ) % 1959 := by
          have h54 : (390625 : ℕ) % 1959 = (784 : ℕ) % 1959 := by
            norm_num
          have h55 : (2 ^ (4 * n) * 7 ^ (2 * n) * 390625) % 1959 = ( (2 ^ (4 * n) * 7 ^ (2 * n)) * 784 ) % 1959 := by
            simp [Nat.mul_mod, h54, Nat.mul_mod]
          exact h55
        omega
      exact h5
  have h5 : (5 ^ (8 * n) : ℕ) % 1959 = (2 ^ (4 * n) * 7 ^ (2 * n)) % 1959 := by
    exact h4 n
  have h6 : 1959 ∣ 5 ^ (8 * n) - 2 ^ (4 * n) * 7 ^ (2 * n) := by
    omega
  exact h6