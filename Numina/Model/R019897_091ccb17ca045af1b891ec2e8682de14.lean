import Mathlib

open Real Set

theorem inequalities_170662 (x : ℝ) :
    sqrt (x + 3) < sqrt (x - 1) + sqrt (x - 2) ↔ x ∈ Ioi (sqrt (28 / 3)) := by
  constructor
  · -- Forward: Assume inequality, prove x > sqrt(28/3)
    intro h
    have h1 : x + 3 ≥ 0 := by
      by_contra h1'
      push_neg at h1'
      have h1'' : sqrt (x + 3) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
        all_goals nlinarith
      rw [h1''] at h
      -- Explicit contradiction
      have h4 : sqrt (x - 1) ≥ 0 := by positivity
      have h5 : sqrt (x - 2) ≥ 0 := by positivity
      -- Check arithmetically that x < -3 for positivity with linarith fails, instead use ordered survey
      have h6 : x < -3 := by nlinarith
      -- Now directly and positivity contradict with Explicit positivity items
      have h7 : sqrt (x - 1) = 0 := by
        have h8 : x - 1 < 0 := by nlinarith
        rw [Real.sqrt_eq_zero']
        linarith
        all_goals nlinarith
      have h8 : sqrt (x - 2) = 0 := by
        have h9 : x - 2 < 0 := by nlinarith
        rw [Real.sqrt_eq_zero']
        linarith
        all_goals nlinarith
      -- Now normalize sqrt with these positivity options (positivity & positivity+)
      norm_num [h7, h8] at h
      <;> nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2)]
    -- Explicit contradiction for positivity contradictions
    have h2 : x - 1 ≥ 0 := by
      by_contra h2'
      push_neg at h2'
      have h7 : sqrt (x - 1) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
        all_goals nlinarith
      have h8 : sqrt (x - 2) = 0 := by
        -- Explicitly handling divide and統制System.log_re Ratio Variants
        by_cases h9 : x - 2 < (0 : ℝ)
        · -- Case where x-2 < 0
          have h10 : sqrt (x - 2) = 0 := by
            rw [Real.sqrt_eq_zero']
            linarith
            all_goals nlinarith
          exact h10
        · -- Case where x - 2 >= 0
          have h10 : x - 2 ≥ 0 := by nlinarith
          -- Now direct systematic check against positivity (Current inconsistencies with normalized positivity)
          exfalso
          have h9' : sqrt (x - 2) ≥ 0 := by positivity
          -- Compare positivity implies (sqrt > choice) pressure
          nlinarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg (x + 3), sq_nonneg (sqrt (x - 2) - sqrt (x - 1)), sq_nonneg (sqrt (x - 2) - 0), sq_nonneg (sqrt (x + 3) - 0), Real.sq_sqrt (show (x + 3) ≥ 0 by linarith), Real.sq_sqrt (show (x - 1) ≥ 0 by nlinarith), Real.sq_sqrt (show (x - 2) ≥ 0 by nlinarith)]
          <;> nlinarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg (x + 3), sq_nonneg (sqrt (x - 2) - sqrt (x - 1)), sq_nonneg (sqrt (x - 2) - 0), sq_nonneg (sqrt (x + 3) - 0)]
      -- Combine all positivity messages into one positivity (positivity operations)
      rw [h7] at h
      -- Explicit positivity leads to positivity contradiction in positivity
      have h9 : x - 1 < 0 := by nlinarith
      have h8 : sqrt (x - 2) ≥ 0 := by positivity
      -- Final positivity
      have h10 : x + 3 ≥ 0 := h1
      -- Apply positivity of squares
      have h5 : sqrt (x + 3) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (x + 3) ≥ 0 by linarith), sq_nonneg (sqrt (x + 3) - 0)]
    -- Normalize positivity messages to positivity
    have h3 : x - 2 ≥ 0 := by
      by_contra h3'
      push_neg at h3'
      have h8 : sqrt (x - 2) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
        all_goals nlinarith
      rw [h8] at h
      have h4 : sqrt (x - 1) ≥ 0 := by positivity
      -- Explicit positivity contradicts positivity
      have h5 : sqrt (x + 3) ≥ 0 := by positivity
      -- Now finally arithmetical to solve positivity
      have h7 : x - 1 ≥ 0 := by nlinarith
      -- Now positivity cannot occur, arithmetical solves
      have h6 : sqrt (x - 1) ^ 2 = x - 1 := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg (x + 3), sq_nonneg (sqrt (x - 2) - sqrt (x - 1)), sq_nonneg (sqrt (x - 2) - 0), sq_nonneg (sqrt (x + 3) - 0), Real.sq_sqrt (show (x + 3) ≥ 0 by linarith), Real.sq_sqrt (show (x - 1) ≥ 0 by nlinarith)]
    -- algebra now stands (positivity contradicts positivity, reach)
    have h5 : sqrt (x + 3) < sqrt (x - 1) + sqrt (x - 2) := h
    have h5' : sqrt (x + 3) ^ 2 < (sqrt (x - 1) + sqrt (x - 2)) ^ 2 := by
      nlinarith [h, Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2)]
    have h6 : (sqrt (x + 3)) ^ 2 = x + 3 := by
      rw [Real.sq_sqrt]
      linarith
    have h7 : (sqrt (x - 1) + sqrt (x - 2)) ^ 2 = (sqrt (x - 1)) ^ 2 + (sqrt (x - 2)) ^ 2 + 2 * sqrt (x - 1) * sqrt (x - 2) := by
      ring
    have h8 : (sqrt (x - 1)) ^ 2 = x - 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h9 : (sqrt (x - 2)) ^ 2 = x - 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h10 : 3 * x ^ 2 > (28 : ℝ) := by
      have h11 : sqrt (x - 1) * sqrt (x - 2) = sqrt ((x - 1) * (x - 2)) := by
        rw [← Real.sqrt_mul (by linarith)]
      nlinarith [h6, h7, h8, h9, h11, Real.sqrt_nonneg ((x - 1) * (x - 2)), Real.sq_sqrt (show (x - 1) * (x - 2) ≥ 0 by nlinarith), Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2)]
    have h11 : x ^ 2 > 28 / 3 := by
      nlinarith
    have h12 : x > Real.sqrt (28 / 3) := by
      by_contra h12
      push_neg at h12
      have h13 : x ^ 2 ≤ 28 / 3 := by
        have h14 : Real.sqrt (28 / 3) ^ 2 = (28 / 3 : ℝ) := by
          exact Real.sq_sqrt (show (28 / 3 : ℝ) ≥ 0 by norm_num)
        nlinarith [h12, h14, Real.sqrt_nonneg (28 / 3), sq_nonneg (x - Real.sqrt (28 / 3))]
      linarith
    exact h12
  · -- Backward: Assume x > sqrt(28/3), prove inequality
    intro h
    have h1 : x > Real.sqrt (28 / 3) := by
      simpa using h
    have h2 : x ^ 2 > 28 / 3 := by
      have h3 : Real.sqrt (28 / 3) ^ 2 = (28 / 3 : ℝ) := by
        exact Real.sq_sqrt (show (28 / 3 : ℝ) ≥ 0 by norm_num)
      nlinarith [h1, h3, Real.sqrt_nonneg (28 / 3), sq_nonneg (x - 2), sq_nonneg (x + 3)]
    have h3 : x + 3 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (28 / 3), h1, Real.sq_sqrt (show (28 / 3 : ℝ) ≥ 0 by norm_num)]
    have h4 : x - 1 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (28 / 3), h1, Real.sq_sqrt (show (28 / 3 : ℝ) ≥ 0 by norm_num)]
    have h5 : x - 2 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (28 / 3), h1, Real.sq_sqrt (show (28 / 3 : ℝ) ≥ 0 by norm_num)]
    have h6 : sqrt (x + 3) < sqrt (x - 1) + sqrt (x - 2) := by
      have h6' : sqrt (x + 3) ^ 2 < (sqrt (x - 1) + sqrt (x - 2)) ^ 2 := by
        have h7 : (sqrt (x + 3)) ^ 2 = x + 3 := by
          rw [Real.sq_sqrt]
          linarith
        have h8 : (sqrt (x - 1) + sqrt (x - 2)) ^ 2 = (sqrt (x - 1)) ^ 2 + (sqrt (x - 2)) ^ 2 + 2 * sqrt (x - 1) * sqrt (x - 2) := by
          ring
        have h9 : (sqrt (x - 1)) ^ 2 = x - 1 := by
          rw [Real.sq_sqrt]
          linarith
          all_goals nlinarith
        have h10 : (sqrt (x - 2)) ^ 2 = x - 2 := by
          rw [Real.sq_sqrt]
          linarith
          all_goals nlinarith
        have h11 : sqrt (x - 1) * sqrt (x - 2) = sqrt ((x - 1) * (x - 2)) := by
          rw [← Real.sqrt_mul (by linarith)]
        -- Substitute positivity directly via positivity
        nlinarith [h7, h8, h9, h10, h11, Real.sqrt_nonneg ((x - 1) * (x - 2)), Real.sq_sqrt (show (x - 1) * (x - 2) ≥ 0 by nlinarith), Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2)]
      have h7 : sqrt (x + 3) ≥ 0 := by positivity
      have h8 : sqrt (x - 1) + sqrt (x - 2) ≥ 0 := by positivity
      nlinarith [h6', Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2)]
    exact h6
  all_goals nlinarith