import Mathlib

theorem algebra_196915 {x y : ℝ} (a b : ℝ) (ha : a = Real.tan x) (hb : b = Real.tan (y / 2))
    (h1 : a + b = 4 / Real.sqrt 3) (h2 : 1 / a + 1 / b = 4 / Real.sqrt 3) :
    (a = Real.sqrt 3 ∧ b = 1 / Real.sqrt 3) ∨ (a = 1 / Real.sqrt 3 ∧ b = Real.sqrt 3) := by

  have h3 : a ≠ 0 := by
    by_contra h
    rw [h] at h1 h2
    have hb0 : b = 4 / Real.sqrt 3 := by linarith
    rw [hb0] at h2
    field_simp at h2
    all_goals
      norm_num [Real.sqrt_ne_zero] at h2

  have h4 : b ≠ 0 := by
    by_contra h
    rw [h] at h1 h2
    have ha0 : a = 4 / Real.sqrt 3 := by linarith
    rw [ha0] at h2
    field_simp at h2
    all_goals
      norm_num [Real.sqrt_ne_zero] at h2

  have h5 : a * b = 1 := by
    have h6 : 1 / a + 1 / b = (a + b) / (a * b) := by
      field_simp [h3, h4]
      all_goals linarith
    rw [h6] at h2
    rw [h1] at h2
    field_simp at h2 ⊢
    all_goals
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]

  have h8 : (a - Real.sqrt 3) * (a - 1 / Real.sqrt 3) = 0 := by
    have h9 : a + b = 4 / Real.sqrt 3 := h1
    have h10 : a * b = 1 := h5
    have h11 : b = 4 / Real.sqrt 3 - a := by linarith
    rw [h11] at h10
    field_simp at h10 ⊢
    nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (a ^ 2 - 1), sq_nonneg (a - Real.sqrt 3), sq_nonneg (a - 1 / Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  cases' (mul_eq_zero.1 h8) with h10 h11
  · -- Case $a = \sqrt{3}$.
    have ha1 : a = Real.sqrt 3 := by linarith
    have hb1 : b = 1 / Real.sqrt 3 := by
      have h12 : a + b = 4 / Real.sqrt 3 := h1
      rw [ha1] at h12
      field_simp at h12 ⊢
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    left
    exact ⟨ha1, hb1⟩
  · -- Case $a = \frac{1}{\sqrt{3}}$.
    have ha2 : a = 1 / Real.sqrt 3 := by
      field_simp at h11 ⊢
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have hb2 : b = Real.sqrt 3 := by
      have h14 : a + b = 4 / Real.sqrt 3 := h1
      rw [ha2] at h14
      field_simp at h14 ⊢
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    right
    exact ⟨ha2, hb2⟩