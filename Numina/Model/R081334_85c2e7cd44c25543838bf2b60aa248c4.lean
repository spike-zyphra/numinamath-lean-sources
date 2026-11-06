import Mathlib

theorem algebra_276528 (x : ℝ) (h : 1 / Real.cos x - Real.tan x = 2) :
    1 / Real.cos x + Real.tan x = 0.5 := by
  have h1 : Real.cos x ≠ 0 := by
    by_contra h2
    have h3 : 1 / Real.cos x = 0 := by
      rw [h2]
      norm_num
      all_goals try { linarith }
    have h4 : Real.tan x = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      rw [h2]
      norm_num
      all_goals try { linarith }
    rw [h3, h4] at h
    all_goals norm_num at h
    all_goals try { linarith }
  have h2 : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [h2] at h
  have eq : 1 / Real.cos x - (Real.sin x / Real.cos x) = (1 - Real.sin x) / Real.cos x := by
    field_simp [h1]
    all_goals ring
  rw [eq] at h
  have h3 : (1 - Real.sin x) / Real.cos x = 2 := h
  have h4 : 1 - Real.sin x = 2 * Real.cos x := by
    field_simp [h1] at h3 ⊢
    all_goals nlinarith
  have h5 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h5a : Real.sin x = 1 - 2 * Real.cos x := by
    linarith
  have h6 : Real.cos x = 4 / 5 := by
    rw [h5a] at h5
    have h6 : (Real.cos x) * (5 * Real.cos x - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- Case h7: Real.cos x = 0
      exfalso
      exact h1 (h7)
    · -- Case h8: 5 * Real.cos x - 4 = 0
      linarith
  have h7 : Real.sin x = -3 / 5 := by
    have h7b : Real.sin x = 1 - 2 * Real.cos x := h5a
    rw [h6] at h7b
    nlinarith
  have h4a : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [h4a]
  rw [show Real.sin x = -3 / 5 by linarith [h7]]
  rw [show Real.cos x = 4 / 5 by linarith [h6]]
  all_goals norm_num
  all_goals try { nlinarith }
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { nlinarith }
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { nlinarith }
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { nlinarith }
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { tauto }