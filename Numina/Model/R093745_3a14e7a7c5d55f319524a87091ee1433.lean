import Mathlib
open Real

theorem algebra_96406 {w d s k : ℝ} (h₀ : 0 < w ∧ 0 < d ∧ 0 < s ∧ 0 < k)
(h₁ : d + s = w + k) (h₂ : d / s = 4 / 3) (h₃ : w = 2 * s) (h₄ : k = 500) :
w + d + s + k = 7000 := by
  have hs : s ≠ 0 := by
    have h_s_pos : 0 < s := h₀.right.right.left
    linarith
  have h₅ : d = 4/3 * s := by
    field_simp [hs] at h₂
    linarith
  rw [h₃, h₄] at h₁
  have h_s_val : s = 1500 := by
    linarith [h₁, h₅]
  have h_d_val : d = 2000 := by
    rw [h_s_val] at h₅
    linarith
  have h_w_val : w = 3000 := by
    linarith [h_s_val, h₃]
  have h_k_val : k = 500 := h₄
  linarith [h_s_val, h_d_val, h_w_val, h_k_val]