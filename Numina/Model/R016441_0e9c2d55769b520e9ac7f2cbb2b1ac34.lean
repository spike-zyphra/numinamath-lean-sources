import Mathlib

theorem algebra_5329 {x y : ℝ} (h1 : (2 : ℝ) ^ (2 * x) + (2 : ℝ) ^ (2 * y) = 320) (h2 : (2 : ℝ) ^ (3 * x) - (2 : ℝ) ^ (3 * y) = -3584) :
    x = 3 ∧ y = 4 := by

  have h3 : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by
    calc
      (2 : ℝ) ^ (2 * x) = (2 ^ (x : ℝ)) ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring; all_goals linarith
      _ = ((2 : ℝ) ^ x) ^ 2 := by norm_num

  have h4 : (2 : ℝ) ^ (2 * y) = ((2 : ℝ) ^ y) ^ 2 := by
    calc
      (2 : ℝ) ^ (2 * y) = (2 ^ (y : ℝ)) ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring; all_goals linarith
      _ = ((2 : ℝ) ^ y) ^ 2 := by norm_num

  have h5 : (2 : ℝ) ^ (3 * x) = ((2 : ℝ) ^ x) ^ 3 := by
    calc
      (2 : ℝ) ^ (3 * x) = (2 ^ (x : ℝ)) ^ 3 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring; all_goals linarith
      _ = ((2 : ℝ) ^ x) ^ 3 := by norm_num

  have h6 : (2 : ℝ) ^ (3 * y) = ((2 : ℝ) ^ y) ^ 3 := by
    calc
      (2 : ℝ) ^ (3 * y) = (2 ^ (y : ℝ)) ^ 3 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring; all_goals linarith
      _ = ((2 : ℝ) ^ y) ^ 3 := by norm_num

  rw [h3, h4] at h1
  rw [h5, h6] at h2

  have h7 : (2 : ℝ) ^ x > 0 := by positivity
  have h8 : (2 : ℝ) ^ y > 0 := by positivity

  have h9 : ((2 : ℝ) ^ x) ^ 2 + ((2 : ℝ) ^ y) ^ 2 = 320 := by linarith
  have h10 : ((2 : ℝ) ^ x) ^ 3 - ((2 : ℝ) ^ y) ^ 3 = -3584 := by linarith

  have h11 : (2 : ℝ) ^ x = 8 := by
    nlinarith [sq_nonneg ((2 : ℝ) ^ x - 8), sq_nonneg ((2 : ℝ) ^ y - 16),
      sq_nonneg ((2 : ℝ) ^ x ^ 2 - 64), sq_nonneg ((2 : ℝ) ^ y ^ 2 - 256),
      Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) x,
      Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) y
      ]
  have h12 : x = 3 := by
    have h13 : (2 : ℝ) ^ (x : ℝ) = (8 : ℝ) := by
      linarith
    have h14 : x = (3 : ℝ) := by
      have h15 : (2 : ℝ) ^ (x : ℝ) = (8 : ℝ) := h13
      have h16 : x = Real.logb (2 : ℝ) (8 : ℝ) := by
        rw [← h15]
        field_simp
      have h17 : Real.logb (2 : ℝ) (8 : ℝ) = (3 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h17] at h16
      linarith
    norm_num at h14 ⊢
    all_goals linarith

  have h17 : (2 : ℝ) ^ (y : ℝ) = (16 : ℝ) := by
    nlinarith [sq_nonneg ((2 : ℝ) ^ x - 8), sq_nonneg ((2 : ℝ) ^ y - 16),
      sq_nonneg ((2 : ℝ) ^ x ^ 2 - 64), sq_nonneg ((2 : ℝ) ^ y ^ 2 - 256),
      Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) x,
      Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) y
      ]
  have h18 : y = 4 := by
    have h19 : (2 : ℝ) ^ (y : ℝ) = (16 : ℝ) := h17
    have h20 : y = (4 : ℝ) := by
      have h21 : (2 : ℝ) ^ (y : ℝ) = (16 : ℝ) := h19
      have h22 : y = Real.logb (2 : ℝ) (16 : ℝ) := by
        rw [← h21]
        field_simp
      have h23 : Real.logb (2 : ℝ) (16 : ℝ) = (4 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h23] at h22
      linarith
    norm_num at h20 ⊢
    all_goals linarith

  exact ⟨h12, h18⟩