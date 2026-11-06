import Mathlib

theorem algebra_219260 {x y : ℝ} (hy : y = Real.sqrt (11 + 6 * Real.sqrt 2)) (hx : x = y - ⌊y⌋) :
    x^2 + 2 * y = 9 := by
  have h1 : y = 3 + Real.sqrt 2 := by
    rw [hy]
    have h2 : Real.sqrt (11 + 6 * Real.sqrt 2) = 3 + Real.sqrt 2 := by
      have h3 : (3 + Real.sqrt 2) ^ 2 = 11 + 6 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      have h4 : 0 ≤ (3 + Real.sqrt 2 : ℝ) := by
        linarith [Real.sqrt_nonneg 2]
      rw [←h3]
      field_simp [Real.sqrt_sq h4]
    exact h2
  have h3 : ⌊y⌋ = 4 := by
    rw [h1]
    have h4 : 4 ≤ (3 + Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    have h5 : (3 + Real.sqrt 2 : ℝ) < (5 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> (try linarith)
  have hx2 : x = Real.sqrt 2 - 1 := by
    rw [hx, h3, h1]
    ring_nf
  rw [hx2, h1]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]