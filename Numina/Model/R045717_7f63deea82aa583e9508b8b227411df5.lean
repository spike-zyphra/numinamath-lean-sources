import Mathlib


theorem number_theory_270199 {b:ℕ} (hb: b ≥ 10):
  Nat.ofDigits b [7, 9, 2] ∣ Nat.ofDigits b [2, 9, 7] ↔
  b = 19 := by
  have h1 : Nat.ofDigits b [7, 9, 2] = 2 * b ^ 2 + 9 * b + 7 := by
    simp [Nat.ofDigits]
    <;> ring
  have h2 : Nat.ofDigits b [2, 9, 7] = 7 * b ^ 2 + 9 * b + 2 := by
    simp [Nat.ofDigits]
    <;> ring
  rw [h1, h2]
  constructor
  · -- Forward direction: divisibility implies b = 19
    intro h
    rcases h with ⟨k, hk⟩
    have h3 : k ≥ 1 := by
      by_contra h7
      push_neg at h7
      have hk1 : k = 0 := by omega
      rw [hk1] at hk
      nlinarith [sq_nonneg (b:ℕ)]
    have h4 : k ≤ 4 := by
      by_contra h6
      push_neg at h6
      have hk6 : k ≥ 5 := by omega
      have h7 : (7 * b ^ 2 + 9 * b + 2 : ℕ) ≥ (5 * (2 * b ^ 2 + 9 * b + 7) : ℕ) := by
        nlinarith [show k ≥ 5 by omega, mul_nonneg (show (0 : ℕ) ≤ (k - 5 : ℕ) by omega) (show (0 : ℕ) ≤ (2 * b ^ 2 + 9 * b + 7) by positivity)]
      -- Contradiction for b ≥ 10
      nlinarith [sq_nonneg (b : ℤ)]
    -- Now we know k ∈ {1, 2, 3, 4}, try each case
    interval_cases k <;> 
      try { 
        ring_nf at hk
        have h6 : b ≤ 19 := by
          nlinarith [sq_nonneg (b ^ 2), sq_nonneg ((b : ℕ) - 19)]
        interval_cases b <;> omega 
      }
  · -- Backward direction: b = 19 implies divisibility
    intro h_eq
    rw [show b = 19 by omega]
    use 3
    all_goals norm_num