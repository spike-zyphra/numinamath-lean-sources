import Mathlib

theorem algebra_2257 (m : ℝ) (h₀ : 0 < m ∧ m < 1) (h₁ : m = √2 - ⌊√2⌋) :
    m^2 + m + √2 = 2 := by

  have h2 : ⌊√2⌋ = 1 := by
    have h3 : 1 < √2 := by
      rw [Real.lt_sqrt] <;> norm_num

    have h4 : √2 < 2 := by
      rw [Real.sqrt_lt] <;> norm_num

    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> (try linarith [h3, h4])

  have hm : m = √2 - 1 := by
    rw [h₁, h2]
    all_goals norm_num

  rw [hm]
  nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]