import Mathlib
theorem algebra_608897 (x : ℝ) (hx : x ≥ 2) : 1 / (√x + √(x - 2)) + 1 / (√x + √(x + 2)) = 1 / 4 ↔ x = 257 / 16:= by
  constructor
  · -- Forward direction: if the equation holds, then x = 257/16
    intro h_eq
    have h1 : 0 < √x + √(x - 2) := by
      have h7 : x ≥ 2 := hx
      have h8 : √x > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h9 : √(x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
      linarith
    have h2 : 0 < √x + √(x + 2) := by
      have h7 : x ≥ 2 := hx
      have h8 : √x > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h9 : √(x + 2) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith
    have eq1 : 1 / (√x + √(x - 2)) = (√x - √(x - 2)) / 2 := by
      have hne : √x + √(x - 2) ≠ 0 := by
        linarith [show √x + √(x - 2) > 0 by linarith [h1]]
      field_simp [hne]
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ x - 2 by nlinarith), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x - 2))]
    have eq2 : 1 / (√x + √(x + 2)) = (√(x + 2) - √x) / 2 := by
      have hne : √x + √(x + 2) ≠ 0 := by
        linarith [show √x + √(x + 2) > 0 by linarith [h2]]
      field_simp [hne]
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 2), Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ x + 2 by nlinarith), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x + 2))]
    rw [eq1, eq2] at h_eq
    have eq3 : √(x + 2) - √(x - 2) = 1 / 2 := by
      nlinarith
    have eq4 : √(x + 2) = √(x - 2) + 1 / 2 := by linarith
    have eq5 : (√(x + 2)) ^ 2 = (√(x - 2) + 1 / 2) ^ 2 := by
      rw [eq4]
    have h3 : (√(x + 2)) ^ 2 = x + 2 := Real.sq_sqrt (by linarith)
    have h4 : (√(x - 2)) ^ 2 = x - 2 := Real.sq_sqrt (by linarith)
    have h5 : (√(x - 2) + 1 / 2) ^ 2 = (√(x - 2)) ^ 2 + 2 * (√(x - 2)) * (1 / 2) + (1 / 2) ^ 2 := by ring
    rw [h5] at eq5
    rw [h3] at eq5
    have eq6 : √(x - 2) = 15 / 4 := by
      nlinarith [Real.sqrt_nonneg (x + 2), Real.sqrt_nonneg (x - 2)]
    have eq7 : x - 2 = 225 / 16 := by 
      calc
        x - 2 = (√(x - 2)) ^ 2 := by 
          rw [Real.sq_sqrt]
          linarith
        _ = (15 / 4) ^ 2 := by
          rw [eq6]
        _ = 225 / 16 := by norm_num
    linarith
  · -- Backward direction: if x = 257/16, then the equation holds
    intro h_eq
    rw [h_eq]
    have h1 : √(257 / 16 : ℝ) = Real.sqrt 257 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h2 : √((257 / 16 : ℝ) - 2) = (15 / 4 : ℝ) := by
      rw [show (257 / 16 : ℝ) - 2 = (225 / 16 : ℝ) by norm_num]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : √((257 / 16 : ℝ) + 2) = (17 / 4 : ℝ) := by
      rw [show (257 / 16 : ℝ) + 2 = (289 / 16 : ℝ) by norm_num]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    field_simp
    nlinarith [Real.sqrt_nonneg 257, Real.sq_sqrt (show (0 : ℝ) ≤ (257 : ℝ) by norm_num)]