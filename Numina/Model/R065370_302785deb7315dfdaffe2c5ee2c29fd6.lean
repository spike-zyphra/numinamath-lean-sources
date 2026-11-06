import Mathlib

theorem algebra_112363 {a : ℝ} (ha : a = 2 ^ ((1 : ℝ) / 3) + 1) :
    (a^3 + a^4) / (a^3 + 1) = 3 := by

  have h1 : a - 1 = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [ha]
    ring

  have h2 : (a - 1) ^ 3 = 2 := by
    rw [h1]
    have h3 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (1 / 3)]
    norm_num at h3 ⊢
    linarith [h3]

  have h_eq : a^3 = 3 * a^2 - 3 * a + 3 := by
    have eq1 : (a - 1) ^ 3 = 2 := h2
    ring_nf at eq1
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]

  have h_eq2 : a ^ 4 = 6 * a^2 - 6 * a + 9 := by
    calc
      a ^ 4 = a * a^3 := by ring
      _ = a * (3 * a^2 - 3 * a + 3) := by rw [h_eq]
      _ = 3 * a^3 - 3 * a^2 + 3 * a := by ring
      _ = 3 * (3 * a^2 - 3 * a + 3) - 3 * a^2 + 3 * a := by rw [h_eq]
      _ = 6 * a^2 - 6 * a + 9 := by ring

  have num_eq : a^3 + a^4 = 9 * a^2 - 9 * a + 12 := by
    calc
      a^3 + a^4 = a^3 + (6 * a^2 - 6 * a + 9) := by rw [h_eq2]
      _ = (3 * a^2 - 3 * a + 3) + (6 * a^2 - 6 * a + 9) := by rw [h_eq]
      _ = 9 * a^2 - 9 * a + 12 := by ring

  have denom_eq : a^3 + 1 = 3 * a^2 - 3 * a + 4 := by
    calc
      a^3 + 1 = (3 * a^2 - 3 * a + 3) + 1 := by rw [h_eq]
      _ = 3 * a^2 - 3 * a + 4 := by ring

  rw [num_eq, denom_eq]

  have h_ne_zero : 3 * a^2 - 3 * a + 4 ≠ 0 := by 
    nlinarith [sq_nonneg (a), sq_nonneg (a - 1), sq_nonneg (a + 1), 
        Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (1 / 3),
        Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (1 / 3)]

  field_simp [h_ne_zero]
  <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]