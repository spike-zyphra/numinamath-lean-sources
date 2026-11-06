import Mathlib

theorem algebra_319788 {α β : ℝ} (h₁ : α^2 - 7 * α + 8 = 0) (h₂ : β^2 - 7 * β + 8 = 0)
    (h₃ : α > β) : (2 / α + 3 * β^2) = (403 - 85 * Real.sqrt 17) / 8 := by
  have h4 : α + β = 7 := by
    have hα : α^2 - 7 * α + 8 = 0 := h₁
    have hβ : β^2 - 7 * β + 8 = 0 := h₂
    have h5 : (α - β) * (α + β - 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- We have h7 : α - β = 0
      linarith
    · -- We have h8 : α + β - 7 = 0
      linarith
  have h5 : α * β = 8 := by
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < (α - β) by linarith), sq_nonneg (α - β), sq_nonneg (α + β - 7)]
  have h8 : (α - (7 + Real.sqrt 17) / 2) * (α - (7 - Real.sqrt 17) / 2) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
  have h9 : α = (7 + Real.sqrt 17) / 2 ∨ α = (7 - Real.sqrt 17) / 2 := by
    cases (mul_eq_zero.mp h8) with
    | inl h10 =>
      left
      linarith
    | inr h11 =>
      right
      linarith
  have h10 : (β - (7 + Real.sqrt 17) / 2) * (β - (7 - Real.sqrt 17) / 2) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
  have h11 : β = (7 + Real.sqrt 17) / 2 ∨ β = (7 - Real.sqrt 17) / 2 := by
    cases (mul_eq_zero.mp h10) with
    | inl h12 =>
      left
      linarith
    | inr h13 =>
      right
      linarith
  cases h9 with
  | inl hα =>
    cases h11 with
    | inl hβ =>
      exfalso
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    | inr hβ =>
      have h12 : α = (7 + Real.sqrt 17) / 2 := hα
      have h13 : β = (7 - Real.sqrt 17) / 2 := hβ
      have h14 : 2 / α = (7 - Real.sqrt 17) / 8 := by
        rw [h12]
        have h5 : (7 + Real.sqrt 17) / 2 ≠ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
        field_simp [h5]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      have h15 : 3 * β^2 = (99 - 21 * Real.sqrt 17) / 2 := by
        rw [h13]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      rw [h14, h15]
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
  | inr hα =>
    cases h11 with
    | inl hβ =>
      exfalso
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    | inr hβ =>
      exfalso
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]