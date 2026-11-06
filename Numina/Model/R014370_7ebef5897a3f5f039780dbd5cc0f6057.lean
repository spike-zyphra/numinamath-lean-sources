import Mathlib

open Real

theorem algebra_296601 {x : ℝ} (hx : x = 1 / sqrt (17 - 12 * sqrt 2)) :
    ⌊x⌋ ^ 2 - ⌊x⌋ * (x - ⌊x⌋) + (x - ⌊x⌋) ^ 2 = 47 - 18 * sqrt 2 := by
  have h0 : sqrt (17 - 12 * sqrt 2) = 3 - 2 * Real.sqrt 2 := by
    have h1 : (3 - 2 * Real.sqrt 2) ^ 2 = (17 - 12 * Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h2 : (3 - 2 * Real.sqrt 2 : ℝ) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [← h1]
    field_simp [Real.sqrt_sq, h2]
  have hx2 : x = 3 + 2 * Real.sqrt 2 := by
    rw [hx]
    rw [h0]
    field_simp [(show (3 - 2 * Real.sqrt 2 : ℝ) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    )
    ]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h2 : ⌊x⌋ = 5 := by
    rw [hx2]
    have h5 : (3 + 2 * Real.sqrt 2 : ℝ) ≥ (5 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
    have h6 : (3 + 2 * Real.sqrt 2 : ℝ) < (6 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try nlinarith
  rw [h2]
  rw [hx2]
  ring_nf
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]