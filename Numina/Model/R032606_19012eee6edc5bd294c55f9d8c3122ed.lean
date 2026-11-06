import Mathlib

open Real

theorem inequalities_282267 {n : ℕ} (hn : n > 0) :
    2 * sqrt (n + 1) - 2 * sqrt n < 1 / sqrt n ∧ 1 / sqrt n < 2 * sqrt n - 2 * sqrt (n - 1) := by
  have h1 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by linarith)
  have h3 : 0 < (sqrt n : ℝ) := by
    apply Real.sqrt_pos.mpr
    positivity
  constructor
  · -- Left inequality: $2\sqrt{n+1}-2\sqrt{n} < \frac{1}{\sqrt{n}}$
    have h4 : 2 * sqrt (n + 1) - 2 * sqrt n < 1 / sqrt n := by
      have h5 : 0 < (sqrt n : ℝ) := h3
      have h6 : (2 * sqrt (n + 1) - 2 * sqrt n) * (sqrt n : ℝ) < 1 := by
        have h7 : (2 * sqrt (n + 1) - 2 * sqrt n) * (sqrt n : ℝ) = 2 * (sqrt (n + 1) * sqrt n) - 2 * (sqrt n) ^ 2 := by
          nlinarith
        rw [h7]
        have h10 : (sqrt n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
        have h11 : (sqrt (n + 1) : ℝ) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (by linarith)
        have h8 : 2 * (sqrt (n + 1) * sqrt n) < (2 * (sqrt n : ℝ) ^ 2 + 1 : ℝ) := by
          have h9 : (2 * (sqrt (n + 1) * sqrt n) : ℝ) ^ 2 < (2 * (sqrt n : ℝ) ^ 2 + 1 : ℝ) ^ 2 := by
            have h10 : (2 * (sqrt (n + 1) * sqrt n) : ℝ) ^ 2 = 4 * ((sqrt (n + 1) * sqrt n) ^ 2) := by ring
            rw [h10]
            have h13 : (2 * (sqrt n : ℝ) ^ 2 + 1 : ℝ) ^ 2 = 4 * ((sqrt n : ℝ) ^ 2) ^ 2 + 4 * ((sqrt n : ℝ) ^ 2) + 1 := by ring
            rw [h13]
            have h14 : (sqrt (n + 1) * sqrt n) ^ 2 = (sqrt (n + 1) : ℝ) ^ 2 * (sqrt n : ℝ) ^ 2 := by
              rw [mul_pow]
            rw [h14, Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith)]
            nlinarith
          have h100 : (2 * (sqrt (n + 1) * sqrt n) : ℝ) ≥ 0 := by positivity
          have h101 : (2 * (sqrt n : ℝ) ^ 2 + 1 : ℝ) ≥ 0 := by positivity
          nlinarith [show (2 * (sqrt (n + 1) * sqrt n) : ℝ) ≥ 0 by positivity, show (2 * (sqrt n : ℝ) ^ 2 + 1 : ℝ) ≥ 0 by positivity]
        nlinarith [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith)]
      have h19 : (2 * sqrt (n + 1) - 2 * sqrt n : ℝ) < (1 / sqrt n : ℝ) := by
        have h20 : (2 * sqrt (n + 1) - 2 * sqrt n : ℝ) < (1 / sqrt n : ℝ) := by
          apply (lt_div_iff₀ (by positivity)).mpr
          nlinarith
        linarith
      linarith
    linarith
  · -- Right inequality: $1 / \sqrt n < 2 \sqrt n - 2 \sqrt (n - 1)$
    by_cases h : n ≥ 1
    · -- n ≥ 1.
      have h15 : (n : ℝ) ≥ 1 := by
        have hn3 : (n : ℝ) ≥ 1 := by exact_mod_cast (show n ≥ 1 by linarith)
        linarith
      have h17 : (n - 1 : ℝ) ≥ 0 := by
        nlinarith
      have h18 : (sqrt (n - 1) : ℝ) ^ 2 = (n - 1 : ℝ) := by
        rw [Real.sq_sqrt]
        linarith
      have h19 : (sqrt (n : ℝ) : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
      have h23 : (1 / sqrt n : ℝ) < (2 * sqrt n - 2 * sqrt (n - 1) : ℝ) := by
        have h30 : (2 * sqrt n - 2 * sqrt (n - 1) : ℝ) > 0 := by
          have h23 : sqrt n > sqrt (n - 1) := by
            apply Real.sqrt_lt_sqrt
            · -- Show 0 ≤ (n - 1 : ℝ)
              nlinarith
            · -- Show (n - 1 : ℝ) < (n : ℝ)
              nlinarith
          nlinarith
        have h24 : (1 / sqrt n : ℝ) < (2 * sqrt n - 2 * sqrt (n - 1) : ℝ) := by
          have h101 : sqrt n > 0 := h3
          apply (div_lt_iff₀ (by positivity)).mpr
          nlinarith [Real.sqrt_nonneg (n - 1 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n - 1 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by nlinarith), sq_nonneg (sqrt n - sqrt (n - 1)), sq_pos_of_pos (show (0 : ℝ) < sqrt n by linarith [h3])]
        linarith
      linarith
    · -- n < 1
      have h9 : n = 0 := by linarith
      omega