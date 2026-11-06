import Mathlib

theorem algebra_4479 (k : ℕ) (hk : 0 < k) (h : 3^k - 1 = 2^(k + 1)) :
    k = 2 := by
  by_cases h1 : k < 3
  · -- k < 3, so k = 1 or 2
    interval_cases k <;> omega
  · -- k >= 3
    have h2 : k ≥ 3 := by omega
    have h3 : ∀ (n : ℕ), n ≥ 3 → 3^n - 1 > 2^(n + 1) := by 
      intro n hn
      have h4 : ∀ (n : ℕ), 3 ^ (n + 3) - 1 > 2 ^ ((n + 3) + 1) := by
        intro n
        induction n with
        | zero =>
          norm_num
        | succ n ih =>
          simp [pow_succ, pow_add, pow_mul, Nat.mul_sub_left_distrib, Nat.sub_mul] at ih ⊢
          all_goals omega
      specialize h4 (n - 3)
      have h5 : n - 3 + 3 = n := by omega
      rw [h5] at h4
      simpa using h4
    have h4 : 3 ^ k - 1 > 2 ^ (k + 1) := by
      specialize h3 k (by omega)
      simpa using h3
    omega