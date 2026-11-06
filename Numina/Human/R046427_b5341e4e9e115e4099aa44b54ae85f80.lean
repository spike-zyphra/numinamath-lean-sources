import Mathlib

open Real

theorem algebra_156823 :
    {x : ℝ | x > 0 ∧ x ^ (logb 10 x) = 100 * x} = {100, 0.1} := by
  ext x
  simp
  constructor
  . intro ⟨hx, h⟩
    apply_fun logb 10 at h
    rw [logb_rpow_eq_mul_logb_of_pos hx,
        logb_mul (by simp) (by positivity),
        show (100 : ℝ) = 10 ^ (2 : ℝ) by norm_num,
        logb_rpow (by simp) (by simp)] at h
    replace h : (logb 10 x - 2) * (logb 10 x - (-1)) = 0 := by linarith only [h]
    simp only [mul_eq_zero, sub_eq_zero] at h
    rcases h with h | h
    all_goals
      apply_fun ((10 : ℝ) ^ ·) at h
      rw [rpow_logb (by simp) (by simp) hx] at h
      norm_num [h]
  . rintro (rfl | rfl)
    . norm_num
      rw [show (100 : ℝ) = 10 ^ (2 : ℝ) by norm_num,
        logb_rpow (by simp) (by simp)]
      norm_num
    . norm_num
      rw [show (1 / 10 : ℝ) = 10 ^ (-1 : ℝ) by norm_num,
          logb_rpow (by simp) (by simp)]
      norm_num
