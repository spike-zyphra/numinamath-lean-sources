import Mathlib

open Real

theorem algebra_191022 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x + y = 13) (h2 : logb 4 x + logb 4 y = 1 + logb 4 10) :
    (x = 5 ∧ y = 8) ∨ (x = 8 ∧ y = 5) := by
  have h3 : x * y = 40 := by
    have h4 : logb 4 x + logb 4 y = logb 4 (x * y) := by
      rw [logb_mul (by positivity) (by positivity)]
    have h5 : (1 : ℝ) + logb 4 10 = logb 4 (4 * 10) := by
      have h6 : (1 : ℝ) = logb 4 4 := by
        rw [logb_self_eq_one (by norm_num)]
        all_goals norm_num
        all_goals simp_all
      rw [h6]
      rw [← logb_mul (by norm_num) (by norm_num)]
      all_goals norm_num
    rw [h4, h5] at h2
    have h7 : x * y = (4 * 10 : ℝ) := by
      have h8 : logb 4 (x * y) = logb 4 (4 * 10) := by linarith
      have h9 : x * y > 0 := by positivity
      have h10 : (4 * 10 : ℝ) > 0 := by norm_num
      have h11 : x * y = (4 * 10 : ℝ) := by
        apply logb_injOn_pos (by norm_num) h9 h10 h8
      exact h11
    nlinarith
  have h4 : y = 13 - x := by linarith
  rw [h4] at h3
  have h5 : x^2 - 13 * x + 40 = 0 := by
    nlinarith
    all_goals nlinarith
    all_goals nlinarith
  have h6 : (x - 5) * (x - 8) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case x = 5
    have hx1 : x = 5 := by linarith
    have hy1 : y = 8 := by linarith [hx1, h4]
    left
    exact ⟨hx1, hy1⟩
  · -- Case x = 8
    have hx2 : x = 8 := by linarith
    have hy2 : y = 5 := by linarith [hx2, h4]
    right
    exact ⟨hx2, hy2⟩