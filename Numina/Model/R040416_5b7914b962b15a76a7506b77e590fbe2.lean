import Mathlib

open Real

theorem algebra_131612 (x : ℕ → ℝ) (hx1 : x 1 = 1)
    (hxn : ∀ n, x (n + 1) = (sqrt 3 * x n + 1) / (sqrt 3 - x n)) :
    x 1999 - x 601 = 0 := by

  have h3 : ∀ n, x (6 * n + 1) = 1 := by
    intro n 
    induction n with 
    | zero =>
      norm_num [hx1]
    | succ n ih =>
      have h4 : x (6 * n + 2) = 2 + Real.sqrt 3 := by 
        rw [show 6 * n + 2 = (6 * n + 1) + 1 by omega]
        rw [hxn]
        rw [ih]
        field_simp [(show Real.sqrt 3 - 1 ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        ), (show Real.sqrt 3 ≠ 0 by positivity)]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sqrt 3 ^ 2 - 3)]
      have h5 : x (6 * n + 3) = - (2 + Real.sqrt 3) := by 
        rw [show 6 * n + 3 = (6 * n + 2) + 1 by omega]
        rw [hxn]
        rw [h4]
        field_simp [(show Real.sqrt 3 - (2 + Real.sqrt 3 : ℝ) ≠ 0 by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        ), (show Real.sqrt 3 ≠ 0 by positivity)]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have h6 : x (6 * n + 4) = -1 := by 
        rw [show 6 * n + 4 = (6 * n + 3) + 1 by omega]
        rw [hxn]
        rw [h5]
        have eq1 : (sqrt 3 * (- (2 + Real.sqrt 3)) + 1) / (sqrt 3 - (- (2 + Real.sqrt 3)) ) = -1 := by
          have h7 : sqrt 3 - (- (2 + Real.sqrt 3)) = 2 * (sqrt 3 + 1) := by 
            ring_nf 
          have h8 : sqrt 3 * (- (2 + Real.sqrt 3)) + 1 = -2 * (sqrt 3 + 1) := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
          rw [h7, h8]
          have h9 : ( -2 * (sqrt 3 + 1) ) / ( 2 * (sqrt 3 + 1) ) = -1 := by
            have h10 : (sqrt 3 + 1) ≠ 0 := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
            field_simp [h10]
            <;> ring
          linarith 
        linarith [eq1]
      have h7 : x (6 * n + 5) = Real.sqrt 3 - 2 := by
        rw [show 6 * n + 5 = (6 * n + 4) + 1 by omega]
        rw [hxn]
        rw [h6]
        field_simp [(show Real.sqrt 3 ≠ 0 by positivity)]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have h8 : x (6 * n + 6) = 2 - Real.sqrt 3 := by 
        rw [show 6 * n + 6 = (6 * n + 5) + 1 by omega]
        rw [hxn]
        rw [h7]
        have eq1 : (sqrt 3 * (Real.sqrt 3 - 2) + 1) / (sqrt 3 - (Real.sqrt 3 - 2) ) = 2 - Real.sqrt 3 := by 
          have h7 : sqrt 3 - (Real.sqrt 3 - 2 : ℝ) = 2 := by 
            ring_nf 
          have h8 : sqrt 3 * (Real.sqrt 3 - 2) + 1 = 4 - 2 * Real.sqrt 3 := by 
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
          rw [h7, h8]
          field_simp 
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        linarith [eq1] 
      have h9 : x (6 * n + 7) = 1 := by 
        rw [show 6 * n + 7 = (6 * n + 6) + 1 by omega]
        rw [hxn]
        rw [h8]
        have eq1 : (sqrt 3 * (2 - Real.sqrt 3) + 1) / (sqrt 3 - (2 - Real.sqrt 3) ) = 1 := by
          have h7 : sqrt 3 - (2 - Real.sqrt 3 : ℝ) = 2 * (sqrt 3 - 1) := by 
            ring_nf
          have h8 : sqrt 3 * (2 - Real.sqrt 3) + 1 = 2 * (sqrt 3 - 1) := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
          rw [h7, h8]
          have h9 : (2 * (sqrt 3 - 1) ) / (2 * (sqrt 3 - 1) ) = 1 := by 
            have h10 : sqrt 3 - 1 ≠ 0 := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
            field_simp [h10]
            <;> ring
          linarith 
        linarith [eq1]
      have : (6 * (n + 1) + 1 : ℕ) = (6 * n + 7 : ℕ) := by omega 
      rw [this]
      exact h9 
  -- Now from this we can compute x 1999 and x 601.
  have h4 : x 1999 = 1 := by
    have h5 : 1999 = 6 * 333 + 1 := by omega
    rw [h5]
    specialize h3 333
    simpa using h3 
  have h5 : x 601 = 1 := by
    have h6 : 601 = 6 * 100 + 1 := by omega
    rw [h6]
    specialize h3 100
    simpa using h3
  rw [h4, h5]
  all_goals norm_num