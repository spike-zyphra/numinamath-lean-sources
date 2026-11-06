import Mathlib

theorem algebra_220172 (x : ℝ) (h : x * (3 + Real.sqrt 5) = 1) :
    x = (3 - Real.sqrt 5) / 4 := by
  have h1 : 3 + Real.sqrt 5 > 0 := by
    have h2 : Real.sqrt 5 > 0 := by
      positivity
    linarith
  
  have h2 : x = 1 / (3 + Real.sqrt 5) := by
    field_simp [(show 3 + Real.sqrt 5 ≠ 0 by linarith)]
    <;> linarith
  
  rw [h2]
  have h3 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  
  field_simp [(show 3 + Real.sqrt 5 ≠ 0 by linarith)]
  <;> ring_nf <;> norm_num [h3] <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)]