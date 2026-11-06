import Mathlib

theorem number_theory_191540 (n : ℕ) :
    2^n ≤ n^2 ↔ n = 2 ∨ n = 3 ∨ n = 4 := by 
  constructor
  · -- Assume 2^n ≤ n^2, prove n = 2 ∨ n = 3 ∨ n = 4
    intro h
    have h1 : n ≤ 4 := by 
      by_contra h2
      push_neg at h2
      have h2' : n ≥ 5 := by omega
      have h3 : ∀ (k : ℕ), k ≥ 5 → 2 ^ k > k ^ 2 := by
        intro k hk
        have base5 : 2 ^ 5 > 5 ^ 2 := by norm_num
        have step : ∀ (i : ℕ), i ≥ 5 → 2 ^ i > i ^ 2 → 2 ^ (i + 1) > (i + 1) ^ 2 := by
          intro i hi h
          have eq1 : 2 ^ (i + 1) = 2 * (2 ^ i) := by ring
          have eq2 : 2 * (2 ^ i) > 2 * (i ^ 2) := by
            have h2 : 2 ^ i > i ^ 2 := h
            nlinarith
          have eq3 : 2 * (i ^ 2) > (i + 1) ^ 2 := by
            nlinarith [sq_nonneg (i : ℕ), sq_nonneg ((i : ℕ) - 1)]
          nlinarith [eq1, eq2, eq3]
        exact Nat.le_induction base5 step k hk
      have h4 : 2 ^ n > n ^ 2 := h3 n (by omega)
      linarith
    interval_cases n <;> norm_num at h ⊢ <;> tauto
  · -- Assume n = 2 ∨ n = 3 ∨ n = 4, prove 2^n ≤ n^2
    rintro (h | h | h)
    · -- n = 2
      rw [h]
      all_goals norm_num
    · -- n = 3 
      rw [h]
      all_goals norm_num
    · -- n = 4
      rw [h]
      all_goals norm_num