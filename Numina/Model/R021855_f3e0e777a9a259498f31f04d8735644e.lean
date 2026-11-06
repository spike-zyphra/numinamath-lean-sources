import Mathlib

theorem algebra_141410 (n : ℕ) (h : 3000 < n * (n - 1) * (n + 1) + n ∧ n * (n - 1) * (n + 1) + n < 4000) :
    n = 15 := by
  have h1 : 3000 < n * (n - 1) * (n + 1) + n := h.1
  have h2 : n * (n - 1) * (n + 1) + n < 4000 := h.2
  by_cases h3 : n ≤ 16
  · interval_cases n <;> omega
  · -- Assume n > 16
    have h4 : n > 16 := by omega
    have h5 : n * (n - 1) * (n + 1) + n ≥ 4000 := by
      have h6 : n ≥ 17 := by linarith
      have h7 : n * (n - 1) * (n + 1) + n ≥ 17 * (17 - 1) * (17 + 1) + 17 := by
        have h10 : n ≥ 17 := by linarith
        have h11 : n * (n - 1) * (n + 1) + n ≥ 17 * (17 - 1) * (17 + 1) + 17 := by
          have h12 : n ≥ 17 := by linarith
          have h13 : n - 1 ≥ 16 := by omega
          have h14 : n + 1 ≥ 18 := by omega
          have h16 : n * (n - 1) * (n + 1) ≥ 17 * (17 - 1) * (17 + 1) := by
            have h17 : n ≥ 17 := by linarith
            have h18 : n - 1 ≥ 16 := by omega
            have h19 : n + 1 ≥ 18 := by omega
            have h20 : n * (n - 1) * (n + 1) ≥ 17 * 16 * 18 := by
              apply Nat.mul_le_mul
              apply Nat.mul_le_mul
              all_goals linarith
            have h21 : 17 * (17 - 1) * (17 + 1) = 17 * 16 * 18 := by norm_num
            rw [h21] at *
            linarith
          have h17 : n ≥ 17 := by linarith
          omega
        linarith
      have h8 : 17 * (17 - 1) * (17 + 1) + 17 ≥ 4000 := by norm_num
      linarith
    linarith