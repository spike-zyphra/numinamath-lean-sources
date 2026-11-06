import Mathlib

open Real

theorem algebra_187727 {x : ℝ} (hx : x > 0 ∧ x ≠ 1) :
    logb x (9 * x ^ 2) * logb 3 x ^ 2 = 4 ↔ x = 1 / 9 ∨ x = 3 := by
  constructor
  · -- Forward direction: if equation holds, then x is 1/9 or 3.
    intro h
    rcases hx with ⟨hx_pos, hx_ne_1⟩
    have h1 : logb x (9 * x ^ 2) = 2 * logb x 3 + 2 := by
      have h2 : logb x (9 * x ^ 2) = logb x 9 + logb x (x ^ 2) := by
        rw [logb_mul (by positivity) (by positivity)]
      have h3 : logb x 9 = 2 * logb x 3 := by
        calc
          logb x 9 = logb x (3 ^ 2) := by norm_num
          _ = 2 * logb x 3 := by simp [logb_pow]
      have h6 : logb x (x ^ 2) = 2 := by
        have h7 : logb x (x ^ 2) = 2 * logb x x := by
          simp [logb_pow]
        have h8 : logb x x = 1 := by
          rw [logb_eq_iff_rpow_eq (show x > 0 by linarith) (show x ≠ 1 by tauto) (show x > 0 by linarith)]
          all_goals norm_num
        rw [h7, h8]
        all_goals norm_num
        all_goals linarith
      rw [h2, h3, h6]
      all_goals linarith
    have h5 : logb x 3 = 1 / logb 3 x := by
      have h6 : logb x 3 = (log 3) / (log x) := by
        field_simp [logb]
      have h7 : logb 3 x = (log x) / (log 3) := by
        field_simp [logb]
      rw [h6, h7]
      <;> field_simp <;> ring
      all_goals linarith
    rw [h1] at h
    rw [h5] at h
    have h6 : 2 * (logb 3 x) ^ 2 + 2 * logb 3 x - 4 = 0 := by
      have h8 : (2 * logb 3 x + 2) * (logb 3 x) ^ 2 = 4 * logb 3 x := by
        field_simp [(show logb 3 x ≠ 0 by
          by_contra h9
          have h10 : logb 3 x = 0 := by
            linarith
          have h11 : x = 1 := by
            have h12 : logb 3 x = 0 := by
              linarith
            rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at h12
            · -- show x = 1
              linarith
            all_goals linarith
          tauto
        )] at h ⊢
        nlinarith
      have h9 : (logb 3 x) ≠ 0 := by
        by_contra h10
        have : logb 3 x = 0 := by linarith
        have h10 : x = 1 := by
          have h11 : logb 3 x = 0 := by
            linarith
          rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at h11
          · -- show x = 1
            linarith
          all_goals linarith
        tauto
      have h10 : (logb 3 x) ^ 2 * (2 * (logb 3 x) + 2) = 4 * (logb 3 x) := by
        nlinarith
      have h11 : 2 * (logb 3 x) ^ 2 + 2 * (logb 3 x) - 4 = 0 := by
        ring_nf at h10 ⊢
        nlinarith [sq_nonneg (logb 3 x), sq_pos_of_ne_zero (show (logb 3 x) ≠ 0 by assumption)]
      linarith
    have h7 : (logb 3 x) ^ 2 + (logb 3 x) - 2 = 0 := by
      nlinarith
    have h8 : (logb 3 x + 2) * (logb 3 x - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Case $\log_3 x + 2 = 0$
      have h11 : logb 3 x = -2 := by linarith
      have h12 : x = (3 : ℝ) ^ (-2 : ℝ) := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at h11
        · -- show x = 1/9
          linarith
        all_goals linarith
      have h13 : x = (1 / 9 : ℝ) := by
        rw [h12]
        norm_num
      left
      exact h13
    · -- Case $\log_3 x - 1 = 0$
      have h14 : logb 3 x = 1 := by linarith
      have h15 : x = (3 : ℝ) ^ (1 : ℝ) := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at h14
        · -- show x = 3
          linarith
        all_goals linarith
      have h16 : x = (3 : ℝ) := by
        rw [h15]
        norm_num
      right
      exact h16
  · -- Backward direction: if x is 1/9 or 3, then equation holds.
    rintro (h_eq | h_eq)
    · -- Case x = 1/9
      rw [h_eq]
      have h1 : logb (1 / 9 : ℝ) (9 * (1 / 9 : ℝ) ^ 2) = 1 := by
        rw [show (9 * (1 / 9 : ℝ) ^ 2 : ℝ) = (1 / 9 : ℝ) by norm_num]
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)]
        all_goals norm_num
      have h2 : logb (3 : ℝ) (1 / 9 : ℝ) = -2 := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)]
        all_goals norm_num
      rw [h1, h2]
      norm_num
      all_goals norm_num
    · -- Case x = 3
      rw [h_eq]
      have h3 : logb (3 : ℝ) (9 * (3 : ℝ) ^ 2) = 4 := by
        rw [show (9 * (3 : ℝ) ^ 2 : ℝ) = (81 : ℝ) by norm_num]
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)]
        all_goals norm_num
      have h4 : logb (3 : ℝ) (3 : ℝ) = 1 := by
        rw [logb_self_eq_one (by norm_num)]
      rw [h3, h4]
      norm_num
      all_goals norm_num