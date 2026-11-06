import Mathlib

theorem algebra_104871 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : Real.sqrt x * (Real.sqrt x - 2 * Real.sqrt y) = Real.sqrt y * (6 * Real.sqrt y - Real.sqrt x)) :
    (x + 2 * Real.sqrt (x * y) + 5 * y) / (2 * x - 3 * Real.sqrt (x * y) + y) = 2 := by
  have h1 : 0 < Real.sqrt x := by
    apply Real.sqrt_pos.mpr
    exact hx
  have h2 : 0 < Real.sqrt y := by
    apply Real.sqrt_pos.mpr
    exact hy
  have h3 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have h4 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h5 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have h6 : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y) := by
    rw [h3]
  have h7 : x - 2 * Real.sqrt (x * y) = 6 * y - Real.sqrt (x * y) := by
    nlinarith [h, h4, h5, Real.sqrt_nonneg x, Real.sqrt_nonneg y, h3]
  have h8 : x - 6 * y = Real.sqrt (x * y) := by
    nlinarith [h7]
  have h9 : (x - 6 * y) ^ 2 = (Real.sqrt (x * y)) ^ 2 := by
    rw [h8]
  have h10 : (Real.sqrt (x * y)) ^ 2 = x * y := Real.sq_sqrt (by positivity)
  have h11 : (x - 6 * y) ^ 2 = x * y := by
    rw [h10] at h9
    linarith
  have h12 : (x - 4 * y) * (x - 9 * y) = 0 := by
    nlinarith [h11]
  cases' (mul_eq_zero.mp h12) with h13 h14
  · -- Case x = 4y. Show it doesn't satisfy the original equation.
    have h15 : x = 4 * y := by linarith
    have h16 : Real.sqrt x = 2 * Real.sqrt y := by
      have h17 : x = 4 * y := h15
      have h18 : Real.sqrt x = Real.sqrt (4 * y) := by
        rw [h17]
      have h19 : Real.sqrt (4 * y) = 2 * Real.sqrt y := by
        have h20 : 4 * y = (2 : ℝ) ^ 2 * y := by
          nlinarith
        rw [h20]
        have h21 : Real.sqrt ((2 : ℝ) ^ 2 * y) = (Real.sqrt ((2 : ℝ) ^ 2)) * (Real.sqrt y) := by
          rw [Real.sqrt_mul (by nlinarith)]
        rw [h21]
        have h22 : Real.sqrt ((2 : ℝ) ^ 2) = (2 : ℝ) := by
          rw [Real.sqrt_sq (by norm_num)]
        rw [h22]
      rw [h18, h19]
    have h0 : Real.sqrt x * (Real.sqrt x - 2 * Real.sqrt y) = Real.sqrt y * (6 * Real.sqrt y - Real.sqrt x) := h
    rw [h16] at h0
    nlinarith [h0, Real.sqrt_nonneg y, Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith), Real.sqrt_pos.mpr hy]
  · -- Case x = 9y.
    have h16 : x = 9 * y := by linarith
    have h17 : Real.sqrt x = 3 * Real.sqrt y := by
      have h18 : x = 9 * y := h16
      have h19 : Real.sqrt x = Real.sqrt (9 * y) := by
        rw [h18]
      have h20 : Real.sqrt (9 * y) = 3 * Real.sqrt y := by
        have h21 : 9 * y = (3 : ℝ) ^ 2 * y := by
          nlinarith
        rw [h21]
        have h22 : Real.sqrt ((3 : ℝ) ^ 2 * y) = (Real.sqrt ((3 : ℝ) ^ 2)) * (Real.sqrt y) := by
          rw [Real.sqrt_mul (by nlinarith)]
        rw [h22]
        have h23 : Real.sqrt ((3 : ℝ) ^ 2) = (3 : ℝ) := by
          rw [Real.sqrt_sq (by norm_num)]
        rw [h23]
      rw [h19, h20]
    have h18 : Real.sqrt (x * y) = 3 * y := by
      have h19 : x * y = (9 * y) * y := by
        have h20 : x = 9 * y := h16
        rw [h20]
      have h20 : (9 * y) * y = (3 * y) ^ 2 := by
        nlinarith
      rw [h19, h20]
      have h21 : Real.sqrt ((3 * y) ^ 2) = 3 * y := by
        rw [Real.sqrt_sq (by nlinarith)]
      rw [h21]
    have h25 : x + 2 * Real.sqrt (x * y) + 5 * y = 20 * y := by
      rw [h18]
      nlinarith [h16]
    have h26 : 2 * x - 3 * Real.sqrt (x * y) + y = 10 * y := by
      rw [h18]
      nlinarith [h16]
    have h27 : (x + 2 * Real.sqrt (x * y) + 5 * y) / (2 * x - 3 * Real.sqrt (x * y) + y) = 2 := by
      rw [h25, h26]
      have hy' : y > 0 := hy
      field_simp [show y > 0 by exact hy']
      <;> nlinarith
    linarith [h27]