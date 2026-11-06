import Mathlib

theorem number_theory_176487 (n : ℕ) (h : n * (n + 1) * (n + 2) * (n + 3) = 110355024) :
    n = 101 := by
  have h1 : n ≤ 107 := by
    by_contra h2
    push_neg at h2
    have h3 : n ≥ 108 := by omega
    have h4 : n * (n + 1) * (n + 2) * (n + 3) > 110355024 := by
      have h5 : n ≥ 108 := by linarith
      have h6 : n * (n + 1) * (n + 2) * (n + 3) ≥ 108 * 109 * 110 * 111 := by
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        all_goals linarith
      have h7 : 108 * 109 * 110 * 111 > 110355024 := by norm_num
      linarith
    linarith
  interval_cases n <;> omega