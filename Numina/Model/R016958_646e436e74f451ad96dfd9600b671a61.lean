import Mathlib

theorem number_theory_114403 (d : ℕ) (hd : d > 1) :
    IsSquare (Nat.ofDigits d [1, 1, 1, 1, 1]) ↔ d = 3 := by
  have h1 : Nat.ofDigits d [1, 1, 1, 1, 1] = d^4 + d^3 + d^2 + d + 1 := by 
    simp [Nat.ofDigits, mul_add, add_mul]
    <;> ring_nf
  rw [h1]
  constructor
  · -- Assume $d^4 + d^3 + d^2 + d + 1$ is a perfect square, prove d = 3
    intro h
    rcases h with ⟨k, hk⟩
    by_cases h' : d ≤ 3
    · -- Assume d ≤ 3.
      have h2 : d = 2 ∨ d = 3 := by 
        omega 
      rcases h2 with (h2 | h2)
      · -- Assume d = 2.
        rw [show d = 2 by omega] at hk 
        norm_num at hk
        have h3 : k ≤ 5 := by 
          nlinarith 
        interval_cases k <;> omega 
      · -- Assume d = 3.
        omega
    · -- Assume d > 3.
      have h5 : d > 3 := by 
        omega 
      have h_eq : k^2 = d^4 + d^3 + d^2 + d + 1 := by 
        nlinarith 
      have h_eq1 : 4 * k^2 = 4 * (d^4 + d^3 + d^2 + d + 1) := by 
        nlinarith [h_eq]
      have h12 : (2 * k) ^ 2 = 4 * (d^4 + d^3 + d^2 + d + 1) := by
        nlinarith [h_eq1]
      have h14 : (d + 1) * (d - 3) > 0 := by 
        have h15 : d - 3 > 0 := by 
          omega 
        have h16 : d + 1 > 0 := by 
          omega 
        nlinarith [h15, h16] 
      -- Bound $k$.
      have h18 : (2 * k) ^ 2 > (2 * d^2 + d) ^ 2 := by
        nlinarith [h12, sq_nonneg ((d : ℕ) ^ 2 : ℕ), sq_nonneg ((d : ℕ) : ℕ), sq_nonneg ((k : ℕ) : ℕ), mul_pos (show 0 < d by omega) (show 0 < d by omega)]
      have h15 : 2 * k > 2 * d^2 + d := by 
        nlinarith [sq_nonneg ((d : ℕ) ^ 2 : ℕ), sq_nonneg ((d : ℕ) : ℕ), sq_nonneg ((k : ℕ) : ℕ)]
      have h20 : (2 * k) ^ 2 < (2 * d^2 + d + 1) ^ 2 := by 
        nlinarith [h12, sq_nonneg (d ^ 2 : ℕ), sq_nonneg (d : ℕ), sq_nonneg (k : ℕ), mul_pos (show 0 < d by omega) (show 0 < d by omega)]
      have h21 : 2 * k < 2 * d^2 + d + 1 := by 
        nlinarith [sq_nonneg (d ^ 2 : ℕ), sq_nonneg (d : ℕ), sq_nonneg (k : ℕ)]
      have h24 : k > d^2 + d / 2 := by 
        omega 
      have h25 : k < d^2 + (d + 1) / 2 := by 
        omega 
      -- Let's observe inconsistency.
      have h24 : k % 2 = 0 ∨ k % 2 = 1 := by 
        omega
      -- Let's observe inconsistency.
      have h27 : k = 11 := by
        nlinarith [sq_nonneg (k : ℕ), sq_nonneg (d^2 : ℕ), sq_nonneg (d : ℕ)]
      -- Bounded k by h24.
      all_goals 
        nlinarith 
  · -- Assume d = 3, prove IsSquare
    intro h
    rw [h]
    use 11
    all_goals 
      norm_num