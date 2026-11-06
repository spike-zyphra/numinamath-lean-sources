import Mathlib

theorem number_theory_257743 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : 1 + 5^a = 6^b) :
    (a, b) = (1, 1) := by
  have h1 : b = 1 := by
    by_cases h2 : b > 1
    · -- Case b > 1
      have h2' : b ≥ 2 := by omega
      have h3 : (6 ^ b : ℕ) % 4 = 0 := by
        have h4 : ∀ k : ℕ, (6 ^ (k + 2 : ℕ) : ℕ) % 4 = 0 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod] at ih ⊢
            all_goals omega
        specialize h4 (b - 2)
        have h5 : b - 2 + 2 = b := by omega
        rw [h5] at h4
        omega
      -- Left side modulo 4
      have h4 : (1 + 5 ^ a) % 4 = 2 := by
        have h5 : (5 : ℕ) % 4 = 1 := by norm_num
        have h6 : (5 ^ a) % 4 = 1 := by
          have h7 : ∀ (a : ℕ), (5 ^ a) % 4 = 1 := by
            intro a
            induction a with
            | zero =>
              norm_num
            | succ a ih =>
              simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod] at ih ⊢
              all_goals omega
          specialize h7 a
          assumption
        omega
      -- Contradiction
      have h5 : (6 ^ b : ℕ) % 4 = 0 := h3
      omega
    · -- Assume b ≤ 1, so b = 1
      have : b = 1 := by linarith
      assumption
  -- Substitute b = 1 into the equation
  have h2 : a = 1 := by
    rw [h1] at h
    have h3 : 5 ^ a = 5 := by
      have h4 : 1 + 5 ^ a = 6 := by
        simpa using h
      have h5 : 5 ^ a = 5 := by
        omega
      assumption
    -- Since 5^a = 5^1, we have a = 1
    have h4 : a = 1 := by
      exact Nat.pow_right_injective (by norm_num) h3
    assumption
  -- Therefore, (a, b) = (1, 1)
  simp [Prod.ext_iff, h2, h1]