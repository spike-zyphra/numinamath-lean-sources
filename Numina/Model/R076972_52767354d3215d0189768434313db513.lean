import Mathlib

theorem algebra_255613 : ∃ k : ℤ, Real.sqrt (7 + Real.sqrt 24) - Real.sqrt (7 - Real.sqrt 24) = k := by
  have h1 : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : Real.sqrt (7 + Real.sqrt 24) = Real.sqrt (7 + 2 * Real.sqrt 6) := by
    rw [h1]
  have h3 : Real.sqrt (7 - Real.sqrt 24) = Real.sqrt (7 - 2 * Real.sqrt 6) := by
    rw [h1]
  -- Show that $\sqrt{7 + 2\sqrt{6}} = \sqrt{6} + 1
  have h4 : Real.sqrt (7 + 2 * Real.sqrt 6) = Real.sqrt 6 + 1 := by
    have h5 : (Real.sqrt 6 + 1) ^ 2 = 7 + 2 * Real.sqrt 6 := by
      calc
        (Real.sqrt 6 + 1) ^ 2 = (Real.sqrt 6) ^ 2 + 2 * Real.sqrt 6 + 1 := by ring
        _ = 6 + 2 * Real.sqrt 6 + 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
        _ = 7 + 2 * Real.sqrt 6 := by ring
    have h6 : Real.sqrt 6 + 1 ≥ 0 := by
      have h7 : Real.sqrt 6 ≥ 0 := Real.sqrt_nonneg 6
      linarith
    rw [←h5]
    field_simp [Real.sqrt_sq (show 0 ≤ Real.sqrt 6 + 1 by linarith [Real.sqrt_nonneg 6])]
    all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num : (0 : ℝ) < (6 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
  -- Show that $\sqrt{7 - 2\sqrt{6}} = \sqrt{6} - 1$
  have h7 : Real.sqrt (7 - 2 * Real.sqrt 6) = Real.sqrt 6 - 1 := by
    have h8 : Real.sqrt 6 ≥ 1 := by
      have h9 : Real.sqrt 6 ≥ Real.sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
      have h10 : Real.sqrt 1 = 1 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith [h9, h10]
      all_goals norm_num
    have h11 : (Real.sqrt 6 - 1) ^ 2 = 7 - 2 * Real.sqrt 6 := by
      calc
        (Real.sqrt 6 - 1) ^ 2 = (Real.sqrt 6) ^ 2 - 2 * Real.sqrt 6 + 1 := by ring
        _ = 6 - 2 * Real.sqrt 6 + 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
        _ = 7 - 2 * Real.sqrt 6 := by ring
    have h12 : Real.sqrt 6 - 1 ≥ 0 := by
      have h13 : Real.sqrt 6 ≥ 1 := h8
      linarith
    rw [←h11]
    field_simp [Real.sqrt_sq (show 0 ≤ Real.sqrt 6 - 1 by linarith [h12, Real.sqrt_nonneg 6])]
    all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num : (0 : ℝ) < (6 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
  use 2
  have eq1 : Real.sqrt (7 + Real.sqrt 24) - Real.sqrt (7 - Real.sqrt 24) = (2 : ℝ) := by
    rw [h2, h3, h4, h7]
    ring
  norm_num at eq1 ⊢
  linarith [eq1]