import Mathlib

theorem algebra_7361 : IsGreatest {n | n < (9 + 4 * Real.sqrt 5)^5 ∧ ∃ k : ℤ, n = k} 1860497 := by
  constructor
  · -- Show that 1860497 is in the set
    constructor
    · -- Show that 1860497 < (9 + 4 * Real.sqrt 5)^5
      have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by linarith)
      have h2 : (9 + 4 * Real.sqrt 5 : ℝ) ^ 5 > (1860497 : ℝ) := by
        nlinarith [h1, Real.sqrt_nonneg 5, sq_nonneg (Real.sqrt 5 ^ 2 * 5 - 5), sq_nonneg (Real.sqrt 5 ^ 3 - 5 * Real.sqrt 5), sq_nonneg (Real.sqrt 5 ^ 4 - 5 ^ 2), sq_nonneg ((9 + 4 * Real.sqrt 5) ^ 2 - 161), sq_nonneg ((9 + 4 * Real.sqrt 5) ^ 2 - (81 + 720 * Real.sqrt 5 + 16 * (Real.sqrt 5 ^ 2)))]
      linarith
    · -- Show that 1860497 is of integer type.
      use 1860497
      all_goals norm_num
  · -- Show that 1860497 is greatest in the set
    intro n hn
    rcases hn with ⟨hn1, ⟨k, hk⟩⟩
    have h1 : Real.sqrt 5 > 0 := by
      positivity
    have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)
    -- Show that 1860497 is indeed the floor of (9 + 4*sqrt(5))^5.
    have h4 : (9 + 4 * Real.sqrt 5) ^ 5 > (1860497 : ℝ) := by
      have h11 : Real.sqrt 5 ^ 2 = 5 := h2
      have h13 : Real.sqrt 5 ^ 4 = 25 := by
        calc
          Real.sqrt 5 ^ 4 = (Real.sqrt 5 ^ 2) ^ 2 := by ring
          _ = (5) ^ 2 := by rw [h11]
          _ = (25 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg 5, h11, sq_nonneg (Real.sqrt 5 ^ 2 - 5), sq_nonneg (Real.sqrt 5 ^ 3 - 5 * Real.sqrt 5), sq_nonneg (Real.sqrt 5 ^ 4 - 25), sq_nonneg ((9 + 4 * Real.sqrt 5) ^ 2 - 161), sq_nonneg ((9 + 4 * Real.sqrt 5) ^ 2 - (81 + 720 * Real.sqrt 5 + 16 * (Real.sqrt 5 ^ 2)))]
    have h5 : (9 + 4 * Real.sqrt 5) ^ 5 < (1860498 : ℝ) := by
      have h11 : Real.sqrt 5 ^ 2 = 5 := h2
      have h13 : Real.sqrt 5 ^ 4 = 25 := by
        calc
          Real.sqrt 5 ^ 4 = (Real.sqrt 5 ^ 2) ^ 2 := by ring
          _ = (5) ^ 2 := by rw [h11]
          _ = (25 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg 5, h11, sq_nonneg (Real.sqrt 5 ^ 2 - 5), sq_nonneg (Real.sqrt 5 ^ 3 - 5 * Real.sqrt 5), sq_nonneg (Real.sqrt 5 ^ 4 - 25), sq_nonneg ((9 + 4 * Real.sqrt 5) ^ 2 - 161), sq_nonneg ((9 + 4 * Real.sqrt 5) ^ 2 - (81 + 720 * Real.sqrt 5 + 16 * (Real.sqrt 5 ^ 2)))]
    have h6 : (k : ℝ) < (1860498 : ℝ) := by
      nlinarith [hn1, h5]
    have h7 : k < 1860498 := by
      by_contra h
      push_neg at h
      have : (k : ℝ) ≥ (1860498 : ℝ) := by
        have h8 : k ≥ 1860498 := by omega
        exact_mod_cast h8
      linarith
    have h8 : k ≤ 1860497 := by
      omega
    have h9 : (k : ℝ) ≤ (1860497 : ℝ) := by
      exact_mod_cast h8
    have h10 : (n : ℝ) = (k : ℝ) := by
      linarith [hk]
    have h11 : (n : ℝ) ≤ (1860497 : ℝ) := by
      linarith [h10, h9]
    linarith [show (n : ℝ) ≤ (1860497 : ℝ) by nlinarith]