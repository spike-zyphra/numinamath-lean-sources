import Mathlib

theorem number_theory_1540 (a b : ℝ) (ha : a = Real.sqrt 11 - ⌊Real.sqrt 11⌋) (hb : b = 1 / a - ⌊1 / a⌋) :
    b = (Real.sqrt 11 - 3) / 2 := by

  have h1 : ⌊Real.sqrt 11⌋ = 3 := by
    have h2 : 3 < Real.sqrt 11 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 11 < 4 := by
      rw [Real.sqrt_lt] <;> norm_num
    have h4 : ⌊Real.sqrt 11⌋ = 3 := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith [h2, h3]
    exact h4
  have ha2 : a = Real.sqrt 11 - 3 := by
    rw [ha, h1]
    all_goals norm_num
  have ha3 : a = Real.sqrt 11 - 3 := ha2
  have h5 : 1 / a = (Real.sqrt 11 + 3) / 2 := by
    rw [ha3]
    have h6 : Real.sqrt 11 - 3 ≠ 0 := by
      have h7 : 3 < Real.sqrt 11 := by
        rw [Real.lt_sqrt] <;> norm_num
      have h8 : Real.sqrt 11 < 4 := by
        rw [Real.sqrt_lt] <;> norm_num
      nlinarith [Real.sqrt_nonneg 11]
    field_simp [h6]
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ (11 : ℝ) by norm_num)]
  have h6 : ⌊1 / a⌋ = 3 := by
    rw [h5]
    have h7 : 3 < (Real.sqrt 11 + 3) / 2 := by
      nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (11 : ℝ) ≥ 0 by norm_num)]
    have h8 : (Real.sqrt 11 + 3) / 2 < (4 : ℝ) := by  -- 4 is >3.5
      nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (11 : ℝ) ≥ 0 by norm_num)]
    have h7' : ⌊ (Real.sqrt 11 + 3) / 2 ⌋ = 3 := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith [h7, h8]
    exact h7'
  rw [hb, h6, h5]
  <;> field_simp <;> nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (11 : ℝ) ≥ 0 by norm_num)]