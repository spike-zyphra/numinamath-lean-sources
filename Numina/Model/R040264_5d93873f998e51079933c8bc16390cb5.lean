import Mathlib

theorem number_theory_7810 (n k : ℕ) :
    ¬ 49 ∣ 2^(n + k) + 2^n + 2^k + 1 := by
  intro h
  have h1 : (2 ^ (n + k) + 2 ^ n + 2 ^ k + 1) % 7 = 0 := by 
    omega 
  have h3 : ∀ (n : ℕ), (2 : ℕ) ^ n % 7 = 1 ∨ (2 : ℕ) ^ n % 7 = 2 ∨ (2 : ℕ) ^ n % 7 = 4 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h1 : (2 : ℕ) ^ (n + 1) % 7 = ((2 : ℕ) ^ n * (2 : ℕ)) % 7 := by ring_nf
      rw [h1]
      rcases ih with (h | h | h)
      ·
        simp [Nat.mul_mod, h]
      ·
        simp [Nat.mul_mod, h]
      ·
        simp [Nat.mul_mod, h]
  have r1 : (2 : ℕ) ^ n % 7 = 1 ∨ (2 : ℕ) ^ n % 7 = 2 ∨ (2 : ℕ) ^ n % 7 = 4 := h3 n
  have r2 : (2 : ℕ) ^ k % 7 = 1 ∨ (2 : ℕ) ^ k % 7 = 2 ∨ (2 : ℕ) ^ k % 7 = 4 := h3 k
  have h4 : (2 ^ (n + k) % 7) = ( (2 ^ n % 7) * (2 ^ k % 7) ) % 7 := by
    have h5 : (2 ^ (n + k) : ℕ) = (2 ^ n * 2 ^ k) := by
      rw [pow_add]
    rw [h5]
    simp [Nat.mul_mod]
  rw [show (2 ^ (n + k) + 2 ^ n + 2 ^ k + 1) % 7 = (2 ^ (n + k) % 7 + (2 ^ n % 7) + (2 ^ k % 7) + 1) % 7 by 
    simp [Nat.add_mod] 
  ] at h1
  rcases r1 with (h11 | h11 | h11) <;> rcases r2 with (h22 | h22 | h22) <;> 
    simp [h4, h11, h22, Nat.add_mod] at h1 <;> omega