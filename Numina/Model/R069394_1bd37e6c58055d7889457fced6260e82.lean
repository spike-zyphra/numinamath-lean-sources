import Mathlib

theorem number_theory_182154 (n : ℕ) : 35 ∣ 3^(6 * n) - 2^(6 * n) := by
  have h5 : (3 ^ (6 * n) - 2 ^ (6 * n)) % 5 = 0 := by
    have h1 : (3 ^ (6 * n)) % 5 = (2 ^ (6 * n)) % 5 := by
      have h3 : (3 ^ (6 * n)) % 5 = ((3 ^ 6) ^ n) % 5 := by
        rw [pow_mul]
      have h4 : (2 ^ (6 * n)) % 5 = ((2 ^ 6) ^ n) % 5 := by
        rw [pow_mul]
      rw [h3, h4]
      have h5 : (3 ^ 6) % 5 = 4 := by norm_num
      have h6 : (2 ^ 6) % 5 = 4 := by norm_num
      have h7 : ((3 ^ 6) ^ n) % 5 = (4 ^ n) % 5 := by
        simp [Nat.pow_mod, h5]
      have h8 : ((2 ^ 6) ^ n) % 5 = (4 ^ n) % 5 := by
        simp [Nat.pow_mod, h6]
      rw [h7, h8]
    omega
  have h7 : (3 ^ (6 * n) - 2 ^ (6 * n)) % 7 = 0 := by
    have h1 : (3 ^ (6 * n)) % 7 = (2 ^ (6 * n)) % 7 := by
      have h3 : (3 ^ (6 * n)) % 7 = 1 := by
        have h4 : (3 ^ (6 * n)) % 7 = ((3 ^ 6) ^ n) % 7 := by
          rw [pow_mul]
        rw [h4]
        have h5 : (3 ^ 6) % 7 = 1 := by norm_num
        have h6 : ((3 ^ 6) ^ n) % 7 = (1 ^ n) % 7 := by
          simp [Nat.pow_mod, h5]
        rw [h6]
        simp
      have h7 : (2 ^ (6 * n)) % 7 = 1 := by
        have h8 : (2 ^ (6 * n)) % 7 = ((2 ^ 6) ^ n) % 7 := by
          rw [pow_mul]
        rw [h8]
        have h9 : (2 ^ 6) % 7 = 1 := by norm_num
        have h10 : ((2 ^ 6) ^ n) % 7 = (1 ^ n) % 7 := by
          simp [Nat.pow_mod, h9]
        rw [h10]
        simp
      omega
    omega
  omega