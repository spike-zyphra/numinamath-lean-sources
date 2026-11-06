import Mathlib

theorem number_theory_125835 (n : ℕ) :
    20 ∣ 9^(8*n+4) - 7^(8*n+4) := by
  have h1 : (9 ^ (8 * n + 4) : ℕ) % 20 = 1 := by 
    have h11 : ∀ m : ℕ, (9 ^ (8 * m + 4) : ℕ) % 20 = 1 := by
      intro m
      induction m with
      | zero =>
        norm_num
      | succ m ih =>
        have h4 : (9 ^ (8 * (m + 1) + 4) : ℕ) = (9 ^ (8 * m + 4) ) * (9 ^ 8) := by 
          ring_nf
        rw [h4]
        simp [Nat.mul_mod, ih]
    specialize h11 n
    simpa using h11

  have h2 : (7 ^ (8 * n + 4) : ℕ) % 20 = 1 := by 
    have h22 : ∀ m : ℕ, (7 ^ (8 * m + 4) : ℕ) % 20 = 1 := by
      intro m
      induction m with
      | zero =>
        norm_num
      | succ m ih =>
        have h4 : (7 ^ (8 * (m + 1) + 4) : ℕ) = (7 ^ (8 * m + 4) ) * (7 ^ 8) := by 
          ring_nf
        rw [h4]
        simp [Nat.mul_mod, ih]
    specialize h22 n
    simpa using h22

  have h5 : (9 ^ (8 * n + 4) - 7 ^ (8 * n + 4) : ℕ) % 20 = 0 := by 
    omega

  omega