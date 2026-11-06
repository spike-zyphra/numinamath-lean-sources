import Mathlib

theorem number_theory_74931 (n : ℕ) :
    ∃ a b c d : ℕ, a^3 + b^3 + c^3 + d^3 = 10^(n^3 - n + 2) := by

  have h1 : n ^ 3 % 3 = n % 3 := by
    have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h2 with (h2 | h2 | h2)
    · simp [h2, pow_succ, Nat.mul_mod]
    · simp [h2, pow_succ, Nat.mul_mod]
    · simp [h2, pow_succ, Nat.mul_mod]

  have h2 : (n ^ 3 - n) % 3 = 0 := by
    omega

  have h3 : ∃ k : ℕ, n ^ 3 - n = 3 * k := by
    refine' ⟨(n ^ 3 - n) / 3, by omega⟩

  rcases h3 with ⟨k, hk⟩
  
  use 10 ^ k
  use 2 * 10 ^ k
  use 3 * 10 ^ k
  use 4 * 10 ^ k

  have h4 : (10 ^ k : ℕ) ^ 3 + (2 * 10 ^ k : ℕ) ^ 3 + (3 * 10 ^ k : ℕ) ^ 3 + (4 * 10 ^ k : ℕ) ^ 3 = 100 * (10 ^ k) ^ 3 := by 
    ring_nf

  have h5 : 100 * (10 ^ k) ^ 3 = 10 ^ (n ^ 3 - n + 2) := by
    have h6 : 3 * k = n ^ 3 - n := by omega

    have h7 : (10 : ℕ) ^ (3 * k) = 10 ^ (n ^ 3 - n) := by 
      rw [show 3 * k = n ^ 3 - n by omega]

    calc
      100 * (10 ^ k) ^ 3 = 100 * (10 ^ (3 * k)) := by ring
      _ = 100 * (10 ^ (n ^ 3 - n)) := by rw [h7]
      _ = 10 ^ 2 * (10 ^ (n ^ 3 - n)) := by norm_num
      _ = 10 ^ (n ^ 3 - n + 2) := by 
        ring_nf

  calc
    (10 ^ k : ℕ) ^ 3 + (2 * 10 ^ k : ℕ) ^ 3 + (3 * 10 ^ k : ℕ) ^ 3 + (4 * 10 ^ k : ℕ) ^ 3 = 100 * (10 ^ k) ^ 3 := h4
    _ = 10 ^ (n ^ 3 - n + 2) := h5