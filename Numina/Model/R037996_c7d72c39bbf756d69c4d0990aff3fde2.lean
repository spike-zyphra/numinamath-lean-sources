import Mathlib

theorem algebra_321278 {a b c : ℝ} (ha : a ≥ 1) (hb : b ≥ 2) (hc : c ≥ 3)
    (h : a + b - 2 * Real.sqrt (a - 1) - 4 * Real.sqrt (b - 2) =
    3 * Real.sqrt (c - 3) - (1 / 2) * c - 5) : a + b + c = 20 := by

  have h1 : (Real.sqrt (a - 1)) ^ 2 = a - 1 := Real.sq_sqrt (by linarith)
  have h2 : (Real.sqrt (b - 2)) ^ 2 = b - 2 := Real.sq_sqrt (by linarith)
  have h3 : (Real.sqrt (c - 3)) ^ 2 = c - 3 := Real.sq_sqrt (by linarith)

  have h4 : (Real.sqrt (a - 1) - 1) ^ 2 + (Real.sqrt (b - 2) - 2) ^ 2 + (1 / 2) * (Real.sqrt (c - 3) - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 2) - 2), sq_nonneg (Real.sqrt (c - 3) - 3), Real.sqrt_nonneg (a - 1), Real.sqrt_nonneg (b - 2), Real.sqrt_nonneg (c - 3), Real.sq_sqrt (show (0 : ℝ) ≤ a - 1 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b - 2 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ c - 3 by linarith)]

  have h5 : (Real.sqrt (a - 1) - 1) ^ 2 = 0 := by
    linarith [h4, sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 2) - 2), sq_nonneg (Real.sqrt (c - 3) - 3)]

  have h6 : (Real.sqrt (b - 2) - 2) ^ 2 = 0 := by
    linarith [h4, sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 2) - 2), sq_nonneg (Real.sqrt (c - 3) - 3)]

  have h7 : (1 / 2) * (Real.sqrt (c - 3) - 3) ^ 2 = 0 := by
    linarith [h4, sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 2) - 2), sq_nonneg (Real.sqrt (c - 3) - 3)]

  have h8 : Real.sqrt (a - 1) - 1 = 0 := by
    rwa [sq_eq_zero_iff] at h5

  have h9 : Real.sqrt (b - 2) - 2 = 0 := by
    rwa [sq_eq_zero_iff] at h6

  have h10 : (Real.sqrt (c - 3) - 3) ^ 2 = 0 := by
    linarith

  have h11 : Real.sqrt (c - 3) - 3 = 0 := by
    rwa [sq_eq_zero_iff] at h10

  have ha1 : Real.sqrt (a - 1) = 1 := by linarith

  have hb1 : Real.sqrt (b - 2) = 2 := by linarith

  have hc1 : Real.sqrt (c - 3) = 3 := by linarith

  have ha2 : a - 1 = 1 := by
    calc
      a - 1 = (Real.sqrt (a - 1)) ^ 2 := by rw [Real.sq_sqrt (by linarith)]
      _ = (1 : ℝ) ^ 2 := by rw [ha1]
      _ = (1 : ℝ) := by norm_num

  have hb2 : b - 2 = 4 := by
    calc
      b - 2 = (Real.sqrt (b - 2)) ^ 2 := by rw [Real.sq_sqrt (by linarith)]
      _ = (2 : ℝ) ^ 2 := by rw [hb1]
      _ = (4 : ℝ) := by norm_num

  have hc2 : c - 3 = 9 := by
    calc
      c - 3 = (Real.sqrt (c - 3)) ^ 2 := by rw [Real.sq_sqrt (by linarith)]
      _ = (3 : ℝ) ^ 2 := by rw [hc1]
      _ = (9 : ℝ) := by norm_num

  have ha3 : a = 2 := by linarith

  have hb3 : b = 6 := by linarith

  have hc3 : c = 12 := by linarith

  linarith [ha3, hb3, hc3]