import Mathlib

open Real
open scoped BigOperators

theorem calculus_22085 :
  arccos ((5*0 + (-3)*(-7) + (-4)*(-1)) / (sqrt (5^2 + (-3)^2 + (-4)^2) * sqrt (0^2 + (-7)^2 + (-1)^2))) * 180 / π = 60 := by
  have h1 : (5 * 0 + (-3) * (-7) + (-4) * (-1) : ℝ) = 25 := by norm_num
  have h2 : sqrt ((5 : ℝ) ^ 2 + (-3) ^ 2 + (-4) ^ 2) = Real.sqrt 50 := by
    norm_num
  have h3 : sqrt ((0 : ℝ) ^ 2 + (-7) ^ 2 + (-1) ^ 2) = Real.sqrt 50 := by
    norm_num
  have h5 : Real.sqrt 50 * Real.sqrt 50 = (50 : ℝ) := by
    calc
      Real.sqrt 50 * Real.sqrt 50 = (Real.sqrt 50) ^ 2 := by ring
      _ = 50 := Real.sq_sqrt (by norm_num)
  have h7 : (5 * 0 + (-3) * (-7) + (-4) * (-1) : ℝ) / (sqrt (5 ^ 2 + (-3) ^ 2 + (-4) ^ 2) * sqrt (0 ^ 2 + (-7) ^ 2 + (-1) ^ 2)) = (1 / 2 : ℝ) := by
    rw [h1, h2, h3]
    have h8 : Real.sqrt 50 * Real.sqrt 50 = (50 : ℝ) := h5
    field_simp [h8]
    <;> norm_num
  rw [h7]
  have h8 : arccos (1 / 2 : ℝ) = Real.pi / 3 := by
    have h9 : cos (Real.pi / 3 : ℝ) = 1 / 2 := cos_pi_div_three
    rw [← h9]
    apply arccos_cos
    all_goals
      linarith [pi_pos]
  rw [h8]
  field_simp [pi_pos]
  <;> ring_nf
  <;> norm_num
  all_goals
    norm_num