import Mathlib

theorem algebra_300616 {x : ℝ} (hx : x = 1 / (3 - Real.sqrt 7)) :
    ⌊x⌋^2 + (1 + Real.sqrt 7) * ⌊x⌋ * (x - ⌊x⌋) = 10 := by
  have h1 : x = (3 + Real.sqrt 7) / 2 := by
    rw [hx]
    have h2 : (3 - Real.sqrt 7 : ℝ) ≠ 0 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    field_simp [h2]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num)]
  
  have h2 : ⌊x⌋ = 2 := by
    rw [h1]
    have h3 : 2 < (3 + Real.sqrt 7) / 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7, show (2 : ℝ) ^ 2 < (7 : ℝ) by norm_num]
    have h4 : (3 + Real.sqrt 7) / 2 < 3 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7, show (7 : ℝ) < (3 : ℝ) ^ 2 by norm_num]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try nlinarith

  rw [h2]
  rw [h1]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), sq_nonneg (Real.sqrt 7 - 2), sq_nonneg (Real.sqrt 7 - 3)]