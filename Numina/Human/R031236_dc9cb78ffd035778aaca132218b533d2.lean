import Mathlib
open Real
/-Find the integer closest to $ \frac { 4 0 4 6 \sqrt { 2 0 2 3 } - 1 } { 2 0 2 3 + \sqrt { 2 0 2 3 } + 1 } $.

Find the integer closest to $ \frac { 4 0 4 6 \sqrt { 2 0 2 3 } - 1 } { 2 0 2 3 + \sqrt { 2 0 2 3 } + 1 } $.-/
theorem algebra_621441 : round (((4046 * √2023 - 1) / (2023 + √2023 + 1)) : ℝ) = 88 := by
  have h1 : 44 < √2023 := by
    rw [Real.lt_sqrt] <;> norm_num
  
  have h2 : √2023 < 45 := by
    rw [Real.sqrt_lt] <;> norm_num

  have h3 : 44.977 < √2023 := by
    rw [Real.lt_sqrt] <;> norm_num
  
  have h4 : √2023 < 44.978 := by
    rw [Real.sqrt_lt] <;> norm_num
  
  have h5 : 87.5 ≤ (4046 * √2023 - 1) / (2023 + √2023 + 1) := by
    have h1 : 0 ≤ (2023 : ℝ) := by norm_num
    have h2 : 0 ≤ √2023 := Real.sqrt_nonneg 2023
    have h3 : 87.5 ≤ (4046 * √2023 - 1) / (2023 + √2023 + 1) := by
      have h5 : 2023 + √2023 + 1 > 0 := by
        linarith [h1, h2]
      apply (le_div_iff₀ h5).mpr
      nlinarith [h3, Real.sq_sqrt (show (0 : ℝ) ≤ 2023 by norm_num), mul_self_nonneg (Real.sqrt 2023 - 44.977)]
    linarith

  have h6 : (4046 * √2023 - 1) / (2023 + √2023 + 1) < 88.5 := by
    have h1 : 0 ≤ (2023 : ℝ) := by norm_num
    have h2 : 0 ≤ √2023 := Real.sqrt_nonneg 2023
    have h3 : (4046 * √2023 - 1) / (2023 + √2023 + 1) < 88.5 := by
      have h5 : 2023 + √2023 + 1 > 0 := by
        linarith [h1, h2]
      apply (div_lt_iff₀ h5).mpr
      nlinarith [h4, Real.sq_sqrt (show (0 : ℝ) ≤ 2023 by norm_num), mul_self_nonneg (Real.sqrt 2023 - 44.978)]
    linarith

  have h7 : round (((4046 * √2023 - 1) / (2023 + √2023 + 1)) : ℝ) = 88 := by
    rw [round_eq]
    simp [Int.floor_eq_iff]
    constructor
    · linarith [h5]
    · linarith [h6]

  exact h7