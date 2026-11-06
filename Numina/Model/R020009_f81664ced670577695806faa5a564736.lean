import Mathlib

theorem number_theory_99445 (a : ℕ) (ha : a ≠ 0) :
    10 ∣ (21^(100 * 3 + 10 * 1 + a) + 32^(100 * a + 10 * 1 + 3) +
        43^(100 * a + 10 * 3 + 1)) := by
  have h1 : (21 ^ (100 * 3 + 10 * 1 + a) : ℕ) % 10 = 1 := by
    have h21 : ∀ (k : ℕ), (21 ^ k : ℕ) % 10 = 1 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        simp [Nat.pow_succ, Nat.mul_mod, ih]
    specialize h21 (100 * 3 + 10 * 1 + a)
    simpa using h21
  have h2 : (32 ^ (100 * a + 10 * 1 + 3) : ℕ) % 10 = 2 := by
    have h32 : ∀ (k : ℕ), (32 ^ (4 * k + 1) : ℕ) % 10 = 2 := by
      intro k 
      induction k with 
      | zero => 
        norm_num 
      | succ k ih =>
        have h4 : (32 ^ (4 * (k + 1) + 1)) % 10 = 2 := by 
          have h5 : (32 ^ (4 * (k + 1) + 1) : ℕ) = (32 ^ (4 * k + 1) : ℕ) * (32 ^ 4 : ℕ) := by 
            ring_nf 
          rw [h5]
          simp [Nat.mul_mod, ih] at *
        exact h4 
    have h3 : (100 * a + 10 * 1 + 3 : ℕ) = 4 * (25 * a + 3) + 1 := by
      omega 
    rw [h3]
    apply h32 (25 * a + 3)
  have h3 : (43 ^ (100 * a + 10 * 3 + 1) : ℕ) % 10 = 7 := by
    have h43 : ∀ (k : ℕ), (43 ^ (4 * k + 3) : ℕ) % 10 = 7 := by 
      intro k 
      induction k with 
      | zero => 
        norm_num 
      | succ k ih =>
        have h6 : (43 ^ (4 * (k + 1) + 3) : ℕ) = (43 ^ (4 * k + 3) : ℕ) * (43 ^ 4 : ℕ) := by 
          ring_nf 
        rw [h6] 
        simp [Nat.mul_mod, ih] at *
    have h4 : (100 * a + 10 * 3 + 1 : ℕ) = 4 * (25 * a + 7) + 3 := by
      omega
    rw [h4]
    apply h43 (25 * a + 7)
  have h4 : ((21 ^ (100 * 3 + 10 * 1 + a) + 32 ^ (100 * a + 10 * 1 + 3) + 43 ^ (100 * a + 10 * 3 + 1)) : ℕ) % 10 = 0 := by 
    omega 
  exact Nat.dvd_of_mod_eq_zero h4