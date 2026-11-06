import Mathlib

open Real

theorem algebra_314685 {a : ℕ → ℝ} (ha : ∀ n, 0 < n → a n = n + 2006 / n ^ 2) :
    IsLeast {x | ∃ n, 0 < n ∧ a n = x} (6102 / 256) := by
  constructor
  · -- Show 6102 / 256 is in the set
    use 16
    constructor
    · norm_num
    · -- Compute a 16 and show it equals 6102 / 256
      specialize ha 16 (by norm_num)
      rw [ha]
      norm_num
  · -- Show the minimality
    intro x hx
    rcases hx with ⟨n, hn, h_eq⟩
    have h1 : a n = n + 2006 / n ^ 2 := ha n hn
    rw [h1] at h_eq
    by_cases h : n ≤ 16
    · -- Case 1: n ≤ 16.
      interval_cases n <;> norm_num [h_eq] at *
      <;> norm_num
      <;> linarith
    · -- Case 2: n > 16.
      have h2 : n ≥ 17 := by omega
      have hn1 : (n : ℝ) ≥ 17 := by exact_mod_cast h2
      have hn2 : (n : ℝ) > 0 := by nlinarith
      have h4 : (n + (2006 / (n ^ 2 : ℝ))) ≥ (6102 / 256 : ℝ) := by
        have h6 : (n + (2006 / (n ^ 2 : ℝ))) - (6102 / 256 : ℝ) ≥ 0 := by
          have h7 : (n + (2006 / (n ^ 2 : ℝ))) - (6102 / 256 : ℝ) =
            ( (n * (n^2 : ℝ) * 256 + 2006 * 256 - 6102 * (n^2 : ℝ) ) / ( (n^2 : ℝ) * 256 ) ) := by
            field_simp [show (n : ℝ) > 0 by linarith]
            <;> ring
          rw [h7]
          have h8 : (n * (n^2 : ℝ) * 256 + 2006 * 256 - 6102 * (n^2 : ℝ)) ≥ 0 := by
            have h9 : (n : ℝ) ≥ 17 := hn1
            have h17 : n * (n^2 : ℝ) * 256 + 2006 * 256 - 6102 * (n^2 : ℝ) ≥ 0 := by
              have h18 : n * (n^2 : ℝ) * 256 ≥ (17^3) * 256 := by
                have hn4 : ((n) : ℝ) ≥ 17 := h9
                have hn5 : (n^2 : ℝ) ≥ (17^2 : ℝ) := by nlinarith [show (n) ≥ (0 : ℝ) by nlinarith]
                have hn6 : ((n) : ℝ) * (n^2 : ℝ) ≥ (17) * (17^2) := by 
                  nlinarith [show (n) ≥ (0 : ℝ) by nlinarith]
                nlinarith [show (n) ≥ (0 : ℝ) by nlinarith]
              have h19 : -6102 * (n^2 : ℝ) ≤ -6102 * (17^2 : ℝ) := by
                have hn4 : ((n) : ℝ) ≥ 17 := h9
                have hn5 : (n^2 : ℝ) ≥ (17^2 : ℝ) := by nlinarith [show (n) ≥ (0 : ℝ) by nlinarith]
                nlinarith [show (n) ≥ (0 : ℝ) by nlinarith]
              nlinarith [show (n) ≥ (0 : ℝ) by nlinarith]
            linarith
          have h9 : (n^2 : ℝ) * 256 > 0 := by
            positivity
          apply div_nonneg
          linarith
          positivity
        linarith
      nlinarith
      <;> nlinarith