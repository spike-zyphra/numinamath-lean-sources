import Mathlib

open Real

theorem algebra_167680 {x : ℝ} (hx : 0 < x) :
    logb 2 x * logb 3 x = logb 3 (x^3) + logb 2 (x^2) - 6 ↔ x = 8 ∨ x = 9 := by
  constructor
  · -- Assume the equation holds, prove x = 8 ∨ x = 9
    intro h_eq
    have h1 : logb 3 (x ^ 3) = 3 * logb 3 x := by
      simp [logb_pow]
    have h2 : logb 2 (x ^ 2) = 2 * logb 2 x := by
      simp [logb_pow]
    rw [h1, h2] at h_eq
    have h3 : (logb 2 x - 3) * (logb 3 x - 2) = 0 := by
      linarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- When $\log_2 x = 3$, then $x = 8$
      have h6 : logb 2 x = 3 := by linarith
      have h7 : x = (2 : ℝ) ^ (3 : ℝ) := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at h6
        · linarith
        all_goals linarith
      have h8 : x = (8 : ℝ) := by
        norm_num at h7 ⊢
        exact_mod_cast h7
      left
      exact_mod_cast h8
    · -- When $\log_3 x = 2$, then $x = 9$
      have h8 : logb 3 x = 2 := by linarith
      have h9 : x = (3 : ℝ) ^ (2 : ℝ) := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at h8
        · linarith
        all_goals linarith
      have h10 : x = (9 : ℝ) := by
        norm_num at h9 ⊢
        exact_mod_cast h9
      right
      exact_mod_cast h10
  · -- Assume x = 8 ∨ x = 9, prove the equation
    rintro (h_eq | h_eq)
    · -- When x = 8
      rw [h_eq]
      have h1 : logb 2 (8 : ℝ) = 3 := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)] <;> norm_num
      have h2 : logb 2 ((8 : ℝ) ^ 2) = 6 := by
        calc
          logb 2 ((8 : ℝ) ^ 2) = logb 2 (64 : ℝ) := by norm_num
          _ = 6 := by
            rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)] <;> norm_num
      have h3 : logb 3 (8 : ℝ) = 3 * logb 3 (2 : ℝ) := by
        calc
          logb 3 (8 : ℝ) = logb 3 ((2 : ℝ) ^ 3) := by norm_num
          _ = 3 * logb 3 (2 : ℝ) := by simp [logb_pow]
      have h4 : logb 3 ((8 : ℝ) ^ 3) = 9 * logb 3 (2 : ℝ) := by
        calc
          logb 3 ((8 : ℝ) ^ 3) = logb 3 ((2 : ℝ) ^ 9) := by norm_num
          _ = 9 * logb 3 (2 : ℝ) := by simp [logb_pow]
      rw [h1, h3, h4, h2]
      linarith
    · -- When x = 9
      rw [h_eq]
      have h4 : logb 3 (9 : ℝ) = 2 := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)] <;> norm_num
      have h5 : logb 3 ((9 : ℝ) ^ 3) = 6 := by
        calc
          logb 3 ((9 : ℝ) ^ 3) = 3 * logb 3 (9 : ℝ) := by simp [logb_pow]
          _ = 3 * 2 := by
            rw [h4]
          _ = (6 : ℝ) := by norm_num
      have h6 : logb 2 (9 : ℝ) = 2 * logb 2 (3 : ℝ) := by
        calc
          logb 2 (9 : ℝ) = logb 2 ((3 : ℝ) ^ 2) := by norm_num
          _ = 2 * logb 2 (3 : ℝ) := by simp [logb_pow]
      have h7 : logb 2 ((9 : ℝ) ^ 2) = 4 * logb 2 (3 : ℝ) := by
        calc
          logb 2 ((9 : ℝ) ^ 2) = logb 2 ((3 : ℝ) ^ 4) := by norm_num
          _ = 4 * logb 2 (3 : ℝ) := by simp [logb_pow]
      rw [h6, h4, h5, h7]
      linarith