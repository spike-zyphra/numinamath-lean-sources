import Mathlib

theorem algebra_177382 {x : ℝ} (hx : x ≥ 1) :
    Real.sqrt (x + Real.sqrt x) - Real.sqrt (x - Real.sqrt x) =
    3 / 2 * Real.sqrt (x / (x + Real.sqrt x)) ↔ x = 25 / 16 := by
  constructor
  · -- Assume the equation holds, prove x = 25/16
    intro h_eq
    have h1 : 0 ≤ x := by linarith
    have h2 : Real.sqrt x ≥ 0 := by positivity
    have h3 : Real.sqrt x ≥ 1 := by
      have h4 : Real.sqrt x ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h5 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    have h4 : Real.sqrt x ≤ x := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]
    have h5 : x - Real.sqrt x ≥ 0 := by
      nlinarith [h4, Real.sqrt_nonneg x]
    have h6 : Real.sqrt (x + Real.sqrt x) ≥ 0 := by positivity
    have h7 : Real.sqrt (x - Real.sqrt x) ≥ 0 := by positivity
    have h8 : Real.sqrt (x / (x + Real.sqrt x)) ≥ 0 := by positivity
    have h13 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    have h9 : x = 25 / 16 := by
      have h10 : Real.sqrt (x + Real.sqrt x) ^ 2 = x + Real.sqrt x := Real.sq_sqrt (by nlinarith)
      have h11 : Real.sqrt (x - Real.sqrt x) ^ 2 = x - Real.sqrt x := by
        apply Real.sq_sqrt
        linarith [h5]
      have h12 : Real.sqrt (x / (x + Real.sqrt x)) ^ 2 = x / (x + Real.sqrt x) := by
        apply Real.sq_sqrt
        have hx1_pos : x + Real.sqrt x > 0 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (x : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith)]
        positivity
      field_simp [h13] at h_eq h10 h11 h12 ⊢
      nlinarith [sq_nonneg (Real.sqrt (x + Real.sqrt x) - Real.sqrt (x - Real.sqrt x) - 3 / 2 * Real.sqrt (x / (x + Real.sqrt x))), sq_nonneg (Real.sqrt x - 5 / 4), Real.sqrt_nonneg (x + Real.sqrt x), Real.sqrt_nonneg (x - Real.sqrt x), Real.sqrt_nonneg (x / (x + Real.sqrt x)), Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x + Real.sqrt x : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (x - Real.sqrt x : ℝ) by nlinarith [h5]), Real.sq_sqrt (show (0 : ℝ) ≤ (x / (x + Real.sqrt x) : ℝ) by positivity)]
    linarith
  · -- Assume x = 25/16, prove the equation
    intro h_eq
    rw [h_eq]
    have h2 : Real.sqrt (25 / 16 : ℝ) = 5 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> linarith
    have h3 : Real.sqrt (25 / 16 + Real.sqrt (25 / 16)) = 3 * Real.sqrt 5 / 4 := by
      rw [h2]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
    have h4 : Real.sqrt (25 / 16 - Real.sqrt (25 / 16)) = Real.sqrt 5 / 4 := by
      rw [h2]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
    have h5 : Real.sqrt ((25 / 16) / (25 / 16 + Real.sqrt (25 / 16))) = Real.sqrt 5 / 3 := by
      rw [h2]
      have h7 : ((25 / 16 : ℝ) / (25 / 16 + (5 / 4 : ℝ))) = (5 / 9 : ℝ) := by
        norm_num
      rw [h7]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h3, h4, h5]
    field_simp
    <;> ring_nf <;> norm_num
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]