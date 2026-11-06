import Mathlib

theorem algebra_201802 {a : ℝ} (h : a / 0.3 = 0.6) : a = 0.18 := by
  have h1 : a = 0.3 * 0.6 := by
    calc
      a = 0.3 * (a / 0.3) := by ring_nf
      _ = 0.3 * 0.6 := by rw [h]
  rw [h1]
  norm_num
  all_goals norm_num at h ⊢ <;> linarith