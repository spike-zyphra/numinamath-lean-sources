import Mathlib
theorem algebra_49900 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : Real.sqrt (3 * x) * (1 + 1 / (x + y)) = 2)
    (h2 : Real.sqrt (7 * y) * (1 - 1 / (x + y)) = 4 * Real.sqrt 2) :
    y / x = 6 := by
  have h3 : 0 < x + y := by linarith
  have eq3 : Real.sqrt (3 * x) * (x + y + 1) = 2 * (x + y) := by
    have h4 : x + y ≠ 0 := by linarith
    field_simp at h1 ⊢
    nlinarith [Real.sqrt_nonneg (3 * x), Real.sqrt_nonneg (7 * y)]
  have eq4 : Real.sqrt (7 * y) * (x + y - 1) = 4 * Real.sqrt 2 * (x + y) := by
    have h4 : x + y ≠ 0 := by linarith
    field_simp at h2 ⊢
    nlinarith [Real.sqrt_nonneg (3 * x), Real.sqrt_nonneg (7 * y)]
  have eq5 : 3 * x * (x + y + 1) ^ 2 = 4 * (x + y) ^ 2 := by
    calc
      3 * x * (x + y + 1) ^ 2 = (Real.sqrt (3 * x) ) ^ 2 * (x + y + 1) ^ 2 := by
        rw [Real.sq_sqrt]
        nlinarith
      _ = (Real.sqrt (3 * x) * (x + y + 1)) ^ 2 := by ring
      _ = (2 * (x + y)) ^ 2 := by
        rw [eq3]
      _ = 4 * (x + y) ^ 2 := by
        ring
  have eq6 : 7 * y * (x + y - 1) ^ 2 = 32 * (x + y) ^ 2 := by
    have h5 : (Real.sqrt (7 * y) ) ^ 2 = 7 * y := by
      apply Real.sq_sqrt
      nlinarith
    have h6 : (4 * Real.sqrt 2) ^ 2 = 32 := by
      calc
        (4 * Real.sqrt 2) ^ 2 = 16 * (Real.sqrt 2) ^ 2 := by ring
        _ = 16 * 2 := by
          rw [Real.sq_sqrt]
          norm_num
        _ = 32 := by
          norm_num
    calc
      7 * y * (x + y - 1) ^ 2 = (Real.sqrt (7 * y)) ^ 2 * (x + y - 1) ^ 2 := by
        rw [Real.sq_sqrt]
        nlinarith
      _ = (Real.sqrt (7 * y) * (x + y - 1)) ^ 2 := by
        ring
      _ = (4 * Real.sqrt 2 * (x + y)) ^ 2 := by
        rw [eq4]
      _ = (4 * Real.sqrt 2) ^ 2 * (x + y) ^ 2 := by
        ring
      _ = 32 * (x + y) ^ 2 := by
        rw [h6]
        all_goals
          ring
  have h4 : y = 6 * x := by
    nlinarith [sq_nonneg (x - y / 6), sq_nonneg ((x + y) - 7 * x), Real.sqrt_nonneg (3 * x), Real.sqrt_nonneg (7 * y), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * x) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (7 * y) by nlinarith), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
  have h5 : y / x = 6 := by
    have h6 : y = 6 * x := h4
    have h7 : x ≠ 0 := by linarith
    field_simp
    linarith
  exact h5