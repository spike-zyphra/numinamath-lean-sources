import Mathlib

theorem algebra_297298 {x : ℕ → ℝ} (hx1 : x 1 = 1)
    (hxn : ∀ n, x (n + 1) = (Real.sqrt 3 * x n + 1) / (Real.sqrt 3 - x n)) :
    x 1999 - x 601 = 0 := by

  have h2 : ∀ n, x (6 * n + 1) = 1 := by
    intro n
    induction n with
    | zero =>
      norm_num [hx1]
    | succ n ih =>
      have h3 : x (6 * n + 2) = 2 + Real.sqrt 3 := by
        have h2' : x (6 * n + 1) = 1 := ih
        specialize hxn (6 * n + 1)
        rw [show 6 * n + 1 + 1 = 6 * n + 2 by omega] at hxn
        rw [h2'] at hxn
        field_simp [(show Real.sqrt 3 - (1 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        )] at hxn ⊢
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

      have h4 : x (6 * n + 3) = -2 - Real.sqrt 3 := by
        have h3' : x (6 * n + 2) = 2 + Real.sqrt 3 := h3
        specialize hxn (6 * n + 2)
        rw [show 6 * n + 2 + 1 = 6 * n + 3 by omega] at hxn
        rw [h3'] at hxn
        field_simp [(show Real.sqrt 3 - (2 + Real.sqrt 3 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        )] at hxn ⊢
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

      have h5 : x (6 * n + 4) = -1 := by
        have h4' : x (6 * n + 3) = -2 - Real.sqrt 3 := h4
        specialize hxn (6 * n + 3)
        rw [show 6 * n + 3 + 1 = 6 * n + 4 by omega] at hxn
        rw [h4'] at hxn
        field_simp [(show Real.sqrt 3 - (-2 - Real.sqrt 3 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        )] at hxn ⊢
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

      have h6 : x (6 * n + 5) = -2 + Real.sqrt 3 := by
        have h5' : x (6 * n + 4) = -1 := h5
        specialize hxn (6 * n + 4)
        rw [show 6 * n + 4 + 1 = 6 * n + 5 by omega] at hxn
        rw [h5'] at hxn
        field_simp [(show Real.sqrt 3 - (-1 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        )] at hxn ⊢
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

      have h7 : x (6 * n + 6) = 2 - Real.sqrt 3 := by
        have h6' : x (6 * n + 5) = -2 + Real.sqrt 3 := h6
        specialize hxn (6 * n + 5)
        rw [show 6 * n + 5 + 1 = 6 * n + 6 by omega] at hxn
        rw [h6'] at hxn
        field_simp [(show Real.sqrt 3 - (-2 + Real.sqrt 3 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        )] at hxn ⊢
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

      have h8 : x (6 * n + 7) = 1 := by
        have h7' : x (6 * n + 6) = 2 - Real.sqrt 3 := h7
        specialize hxn (6 * n + 6)
        rw [show 6 * n + 6 + 1 = 6 * n + 7 by omega] at hxn
        rw [h7'] at hxn
        field_simp [(show Real.sqrt 3 - (2 - Real.sqrt 3 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        )] at hxn ⊢
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

      rw [show 6 * (n + 1) + 1 = 6 * n + 7 by omega]
      exact h8

  have h3 : x 1999 = 1 := by
    have h4 : 1999 = 6 * 333 + 1 := by norm_num
    rw [h4]
    specialize h2 333
    simpa using h2

  have h4 : x 601 = 1 := by
    have h5 : 601 = 6 * 100 + 1 := by norm_num
    rw [h5]
    specialize h2 100
    simpa using h2

  rw [h3, h4]
  all_goals norm_num