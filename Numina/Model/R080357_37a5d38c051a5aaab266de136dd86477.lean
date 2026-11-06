import Mathlib

open Real

theorem algebra_100014 (x : ℝ) (hx : x = -79 / 4) :
    1 / (sqrt (x + 20) + sqrt (x + 21)) + 1 / (sqrt (x + 21) + sqrt (x + 22)) = 1 := by
  rw [hx]
  have h1 : sqrt (-79 / 4 + 20) = 1 / 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h3 : sqrt (-79 / 4 + 21) = Real.sqrt 5 / 2 := by
    have h_eq : (-79 / 4 + 21) = (Real.sqrt 5 / 2)^2 := by
      have h_sq : Real.sqrt 5^2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith
  
    rw [h_eq]
    have h_pos : 0 ≤ Real.sqrt 5 / 2 := by
      have h5_pos : 0 ≤ Real.sqrt 5 := by positivity
      nlinarith
  
    rw [Real.sqrt_sq h_pos]

  have h2 : sqrt (-79 / 4 + 22) = 3 / 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  
  rw [h1, h3, h2]
  have h5 : Real.sqrt 5 ^ 2 = 5 := by
    exact sq_sqrt (by norm_num)
  
  have h6 : Real.sqrt 5 > 0 := by
    positivity
  
  field_simp [(show (1 / 2 + Real.sqrt 5 / 2) ≠ 0 by 
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]), (show (Real.sqrt 5 / 2 + 3 / 2) ≠ 0 by 
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)])]
  <;> ring_nf
  <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]