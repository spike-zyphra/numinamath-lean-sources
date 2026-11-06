import Mathlib

theorem Real.rpow_right_inj : ∀ {x y z : ℝ}, 0 < x → x ≠ 1 → (x ^ y = x ^ z ↔ y = z) := sorry

open Real

theorem algebra_196050 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x ^ (Real.logb 3 y) + 2 * y ^ (Real.logb 3 x) = 27) (h2 : Real.logb 3 y - Real.logb 3 x = 1) :
    (x = 3 ∧ y = 9) ∨ (x = 1 / 9 ∧ y = 1 / 3) := by
  have : y ^ logb 3 x = x ^ logb 3 y := by
    rw [← (logb_injOn_pos (show (1:ℝ)<3 by norm_num)).eq_iff]
    repeat rw [logb_rpow_eq_mul_logb_of_pos]
    ring; any_goals simp
    all_goals positivity
  replace h1 : x ^ logb 3 y = 9 := by
    linarith only [this, h1]
  rw [sub_eq_iff_eq_add] at h2; rw [h2] at h1
  nth_rw 1 [← rpow_logb (show (0:ℝ)<3 by norm_num) (by norm_num) hx] at h1
  rw [← rpow_mul, show (9:ℝ) = 3^(2:ℝ) by norm_num] at h1
  rw [rpow_right_inj, ← sub_eq_zero] at h1
  simp [show logb 3 x * (1 + logb 3 x) - 2 = (logb 3 x + 2) * (logb 3 x - 1) by ring] at h1
  rcases h1 with h1|h1
  · rw [← eq_neg_iff_add_eq_zero] at h1; rw [h1] at h2
    rw [logb_eq_iff_rpow_eq] at h1 h2
    norm_num at h1 h2; simp [h1, h2]
    any_goals norm_num
    all_goals assumption
  rw [sub_eq_zero] at h1; rw [h1] at h2
  rw [logb_eq_iff_rpow_eq] at h1 h2
  norm_num at h1 h2; simp [h1, h2]
  any_goals norm_num
  all_goals assumption