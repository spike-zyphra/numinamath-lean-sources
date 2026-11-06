import Mathlib

theorem algebra_287434 {h r : ℝ}
    (hh : 3 * 60 / h - 3 * 60 / (4 * h) = 27)
    (hr : 6 * 60 / r - 6 * 60 / (4 * r) = 120) : 
    h = 5 ∧ r = 2.25 := by
  by_cases h₀: h = 0
  · rw [h₀] at hh
    norm_num at hh
  by_cases h₁: r = 0
  · rw [h₁] at hr
    norm_num at hr
  rw [←div_div] at *
  norm_num at *
  field_simp at *
  constructor <;> linarith