import Mathlib

theorem number_theory_3051 (n : ℕ) (h₀ : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) = 32432400) :
    n + 6 = 15 := by
  have h2 : n ≤ 9 := by
    by_contra h
    push_neg at h
    have h3 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) > 32432400 := by
      have h4 : n ≥ 10 := by
        omega
      have h3' : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) ≥ 10 * 11 * 12 * 13 * 14 * 15 * 16 := by
        have h7 : n ≥ 10 := h4
        have h8 : n + 1 ≥ 11 := by omega
        have h9 : n + 2 ≥ 12 := by omega
        have h10 : n + 3 ≥ 13 := by omega
        have h11 : n + 4 ≥ 14 := by omega
        have h12 : n + 5 ≥ 15 := by omega
        have h13 : n + 6 ≥ 16 := by omega
        have h14 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) ≥ 10 * 11 * 12 * 13 * 14 * 15 * 16 := by
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          all_goals
            omega
        linarith
      nlinarith
    nlinarith
  interval_cases n <;> omega