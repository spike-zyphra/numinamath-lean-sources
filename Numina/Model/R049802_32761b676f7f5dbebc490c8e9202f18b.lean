import Mathlib

theorem algebra_1692
    (a b c : ℝ)
    (ha : 3 ≤ a)
    (hb : 3 ≤ b)
    (hc : 3 ≤ c) :
    2 + Real.sqrt 2 ≤ Real.sqrt (a - 2) + Real.sqrt (b + 1) + abs (1 - Real.sqrt (c - 1)) := by
  have h1 : Real.sqrt (a - 2) ≥ 1 := by
    have h1 : a - 2 ≥ (1 : ℝ) := by linarith
    have h2 : Real.sqrt (a - 2) ≥ Real.sqrt (1 : ℝ) := by
      apply Real.sqrt_le_sqrt (by linarith)
    have h3 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    linarith [h2, h3]

  have h2 : Real.sqrt (b + 1) ≥ 2 := by
    have h1 : b + 1 ≥ (4 : ℝ) := by linarith
    have h2 : Real.sqrt (b + 1) ≥ Real.sqrt (4 : ℝ) := by
      apply Real.sqrt_le_sqrt (by linarith)
    have h3 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith [h2, h3]

  have h3 : Real.sqrt (c - 1) ≥ Real.sqrt 2 := by
    have h1 : c - 1 ≥ (2 : ℝ) := by linarith
    have h2 : Real.sqrt (c - 1) ≥ Real.sqrt (2 : ℝ) := by
      apply Real.sqrt_le_sqrt (by linarith)
    linarith [h2]

  have h4 : abs (1 - Real.sqrt (c - 1)) ≥ Real.sqrt 2 - 1 := by
    have h5 : Real.sqrt (c - 1) > 1 := by
      have h6 : c - 1 ≥ (2 : ℝ) := by linarith
      have h7 : Real.sqrt (c - 1) ≥ Real.sqrt (2 : ℝ) := by
        apply Real.sqrt_le_sqrt (by linarith)
      have h8 : Real.sqrt (2 : ℝ) > (1 : ℝ) := by
        have h9 : (1 : ℝ) < Real.sqrt 2 := by
          rw [Real.lt_sqrt] <;> norm_num
        linarith [h9]
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (c - 1), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ c - 1 by linarith)]
    have h6 : 1 - Real.sqrt (c - 1) < (0 : ℝ) := by linarith [h5, Real.sqrt_nonneg (c - 1)]
    have h7 : abs (1 - Real.sqrt (c - 1)) = Real.sqrt (c - 1) - 1 := by
      rw [abs_of_neg h6]
      all_goals linarith [Real.sqrt_nonneg (c - 1), h5]
    have h8 : Real.sqrt (c - 1) - 1 ≥ Real.sqrt 2 - 1 := by
      have h9 : Real.sqrt (c - 1) ≥ Real.sqrt 2 := by
        linarith [show Real.sqrt 2 ≥ 0 by positivity, h3]
      linarith [Real.sqrt_nonneg 2, h9]
    linarith [h7, h8]

  have h5 : Real.sqrt (a - 2) + Real.sqrt (b + 1) + abs (1 - Real.sqrt (c - 1)) ≥ 2 + Real.sqrt 2 := by
    have h6 : Real.sqrt (a - 2) ≥ (1 : ℝ) := h1
    have h7 : Real.sqrt (b + 1) ≥ (2 : ℝ) := h2
    have h8 : abs (1 - Real.sqrt (c - 1)) ≥ Real.sqrt 2 - 1 := h4
    linarith [h6, h7, h8]

  linarith [h5, Real.sqrt_nonneg 2, Real.sqrt_nonneg (a - 2), Real.sqrt_nonneg (b + 1)]