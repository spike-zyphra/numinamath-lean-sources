import Mathlib

theorem algebra_312340 {a b : ℝ} (ha : a = Real.sqrt 11 - ⌊Real.sqrt 11⌋) (hb : b = 1 / a - ⌊1 / a⌋) :
    b = (Real.sqrt 11 - 3) / 2 := by

  have h1 : ⌊Real.sqrt 11⌋ = 3 := by 
    have h2 : 3 < Real.sqrt 11 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 11 < (4 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    have h4 : ⌊Real.sqrt 11⌋ = 3 := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    exact h4

  have ha2 : a = Real.sqrt 11 - 3 := by
    rw [ha, h1]
    all_goals norm_num

  have h5 : 1 / a = (Real.sqrt 11 + 3) / 2 := by
    rw [ha2]
    have h6 : Real.sqrt 11 - 3 ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    field_simp [h6]
    <;> nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]

  have h7 : ⌊1 / a⌋ = 3 := by
    rw [h5]
    have h8 : 3 < (Real.sqrt 11 + 3) / 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    have h9 : (Real.sqrt 11 + 3) / 2 < (4 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    have h10 : ⌊(Real.sqrt 11 + 3) / 2⌋ = 3 := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    exact h10
  
  rw [hb, h7, h5]
  all_goals linarith