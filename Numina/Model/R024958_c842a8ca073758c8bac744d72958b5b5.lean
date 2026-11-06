import Mathlib

theorem number_theory_218685 (n : ℕ) : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) ≠ 776965920 := by 
  by_contra h
  have h1 : n ≤ 43 := by
    by_contra h2
    push_neg at h2
    have h2' : n ≥ 44 := by omega
    have h3 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) ≥ 44 * 45 * 46 * 47 * 48 * 49 := by
      have h4 : n ≥ 44 := h2'
      have h5 : n + 1 ≥ 45 := by omega
      have h6 : n + 2 ≥ 46 := by omega
      have h7 : n + 3 ≥ 47 := by omega
      have h8 : n + 4 ≥ 48 := by omega
      have h9 : n + 5 ≥ 49 := by omega
      have h10 : (n : ℕ) * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) ≥ 44 * 45 * 46 * 47 * 48 * 49 := by
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        all_goals linarith
      linarith
    nlinarith
  interval_cases n <;> omega