import Mathlib

theorem algebra_241760 (x : ℝ) (hx : x ≠ -1 / 2) :
    x ^ 4 / (2 * x + 1) + x ^ 2 = 6 * (2 * x + 1) ↔
    x = -3 - Real.sqrt 6 ∨ x = 2 + Real.sqrt 6 ∨ x = -3 + Real.sqrt 6 ∨ x = 2 - Real.sqrt 6 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    have h1 : 2 * x + 1 ≠ 0 := by
      intro h2
      have : x = -1 / 2 := by linarith
      contradiction
    have eq1 : x ^ 4 + 2 * x ^ 3 - 23 * x ^ 2 - 24 * x - 6 = 0 := by
      have eq2 : x ^ 4 / (2 * x + 1) + x ^ 2 = 6 * (2 * x + 1) := h
      have eq3 : x ^ 4 / (2 * x + 1) + x ^ 2 = (x ^ 4 + x ^ 2 * (2 * x + 1)) / (2 * x + 1) := by
        field_simp [show 2 * x + 1 ≠ 0 by assumption]
        <;> nlinarith
      rw [eq3] at eq2
      have eq4 : (x ^ 4 + x ^ 2 * (2 * x + 1)) / (2 * x + 1) = 6 * (2 * x + 1) := by
        linarith
      have eq5 : x ^ 4 + x ^ 2 * (2 * x + 1) = 6 * (2 * x + 1) * (2 * x + 1) := by
        have h2 : 2 * x + 1 ≠ 0 := by assumption
        field_simp [h2] at eq4 ⊢
        <;> nlinarith
      nlinarith
      <;> nlinarith
    have h2 : (x ^ 2 + 6 * x + 3) * (x ^ 2 - 4 * x - 2) = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 3), sq_nonneg (x - 2)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- First factor equals zero
      have h5 : x ^ 2 + 6 * x + 3 = 0 := by linarith
      have h6 : x ^ 2 + 6 * x + 3 = (x - (-3 - Real.sqrt 6)) * (x - (-3 + Real.sqrt 6)) := by
        nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      rw [h6] at h5
      cases' (mul_eq_zero.mp h5) with h7 h8
      · -- First root
        left
        linarith
        <;> nlinarith
      · -- Second root
        right
        right
        left
        nlinarith
        <;> nlinarith
    · -- Second factor equals zero
      have h9 : x ^ 2 - 4 * x - 2 = 0 := by linarith
      have h10 : x ^ 2 - 4 * x - 2 = (x - (2 + Real.sqrt 6)) * (x - (2 - Real.sqrt 6)) := by
        nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      rw [h10] at h9
      cases' (mul_eq_zero.mp h9) with h11 h12
      · -- First root
        right
        left
        linarith
        <;> nlinarith
      · -- Second root
        right
        right
        right
        linarith
        <;> nlinarith
  · -- Assume right side, prove left side
    rintro (h | h | h | h)
    · -- Case x = -3 - Real.sqrt 6
      rw [h]
      field_simp [(show 2 * (-3 - Real.sqrt 6) + 1 ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      )]
      nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    · -- Case x = 2 + Real.sqrt 6
      rw [h]
      field_simp [(show 2 * (2 + Real.sqrt 6) + 1 ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      )]
      nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    · -- Case x = -3 + Real.sqrt 6
      rw [h]
      field_simp [(show 2 * (-3 + Real.sqrt 6) + 1 ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      )]
      nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    · -- Case x = 2 - Real.sqrt 6
      rw [h]
      field_simp [(show 2 * (2 - Real.sqrt 6) + 1 ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      )]
      nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]