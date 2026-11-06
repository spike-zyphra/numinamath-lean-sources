import Mathlib

theorem algebra_101522 {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
  (h3 : c ≠ a) (h4 : a^2 + b * c = 115) (h5 : b^2 + a * c = 127)
  (h6 : c^2 + a * b = 115) : a + b + c = 22 := by
  apply_fun fun t => t - 115 at h6
  nth_rw 1 [← h4, sub_self] at h6
  simp [show  c ^ 2 + a * b - (a ^ 2 + b * c) = (c - a) * (c + a - b) by ring] at h6
  rw [sub_eq_zero] at h6; rcases h6 with h6|h6
  · simp [h6] at h3
  rw [sub_eq_zero, add_comm] at h6; rw [← h6] at h4 h5
  rw [show a ^ 2 + (a + c) * c = a ^ 2 + c ^ 2 + a * c by ring] at h4
  rw [show (a + c) ^ 2 + a * c = a ^ 2 + c ^ 2 + 3 * (a * c) by ring] at h5
  replace h5 : a * c = 6 := by linarith
  apply_fun fun t => t + 6 at h4
  nth_rw 1 [← h5, show (115:ℝ)+6 = 11^2 by norm_num] at h4
  rw [show a ^ 2 + c ^ 2 + a * c + a * c = (a + c) ^ 2 by ring] at h4
  rw [pow_left_inj₀] at h4
  rw [h4] at h6; rw [show a+b+c = a+c+b by ring, h4, ← h6]
  norm_num
  all_goals positivity