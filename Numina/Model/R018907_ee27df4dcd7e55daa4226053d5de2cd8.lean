import Mathlib

theorem algebra_4824 : ⌊(√2 + √3)^8⌋ = 9601 := by
  have h1 : (√2 + √3) ^ 2 = 5 + 2 * √6 := by
    calc
      (√2 + √3) ^ 2 = (√2) ^ 2 + (√3) ^ 2 + 2 * (√2 * √3) := by ring
      _ = 2 + 3 + 2 * (√2 * √3) := by simp [Real.sq_sqrt]
      _ = 5 + 2 * (√2 * √3) := by ring
      _ = 5 + 2 * (√(2 * 3)) := by
        rw [← Real.sqrt_mul (by norm_num)]
      _ = 5 + 2 * √6 := by norm_num

  have h2 : (√2 + √3) ^ 4 = 49 + 20 * √6 := by
    calc
      (√2 + √3) ^ 4 = ((√2 + √3) ^ 2) ^ 2 := by ring
      _ = (5 + 2 * √6) ^ 2 := by rw [h1]
      _ = 49 + 20 * √6 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]

  have h3 : (√2 + √3) ^ 8 = (49 + 20 * √6) ^ 2 := by
    calc
      (√2 + √3) ^ 8 = ((√2 + √3) ^ 4) ^ 2 := by ring
      _ = (49 + 20 * √6) ^ 2 := by rw [h2]

  have h4 : (√2 + √3) ^ 8 = 4801 + 1960 * √6 := by
    rw [h3]
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]

  have h4' : (√2 + √3) ^ 8 = 4801 + 1960 * √6 := h4

  rw [h4']
  have h7 : ⌊(4801 + 1960 * √6 : ℝ)⌋ = 9601 := by
    rw [Int.floor_eq_iff]
    constructor
    · -- Show that 9601 ≤ 4801 + 1960*√6
      norm_num at *
      all_goals nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]
    · -- Show that 4801 + 1960*√6 < 9601 + 1
      norm_num at *
      all_goals nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]
  exact h7