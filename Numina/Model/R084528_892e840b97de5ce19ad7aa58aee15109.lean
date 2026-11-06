import Mathlib

theorem algebra_184269 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ 1) (hbc : b ≠ 1) :
    Real.logb a b * Real.logb b c = Real.logb a c := by
  have h1 : Real.logb a b = Real.log b / Real.log a := by 
    field_simp [Real.logb]
  have h2 : Real.logb b c = Real.log c / Real.log b := by 
    field_simp [Real.logb]
  have h3 : Real.logb a c = Real.log c / Real.log a := by 
    field_simp [Real.logb]

  rw [h1, h2, h3]

  have h4 : Real.log a ≠ 0 := by
    have h_pos : 0 < a := ha
    have h_ne_1 : a ≠ 1 := hab
    exact Real.log_ne_zero_of_pos_of_ne_one h_pos h_ne_1

  have h5 : Real.log b ≠ 0 := by
    have h_pos : 0 < b := hb
    have h_ne_1 : b ≠ 1 := hbc
    exact Real.log_ne_zero_of_pos_of_ne_one h_pos h_ne_1
  
  field_simp [h4, h5]
  <;> ring_nf <;> field_simp [h4, h5] <;> nlinarith