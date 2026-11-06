import Mathlib

open Real

theorem algebra_186632 : (arctan (2 + sqrt 5) + arctan (1 / (2 - sqrt 5))) < 5 * sqrt 7 / 4 := by 
  have h1 : 1 / (2 - sqrt 5) = -(2 + sqrt 5) := by 
    field_simp [show 2 - sqrt 5 ≠ 0 by 
      intro h
      have : sqrt 5 = (2 : ℝ) := by linarith 
      have : (5 : ℝ) = (2 : ℝ) ^ 2 := by 
        calc 
          (5 : ℝ) = (sqrt 5) ^ 2 := by rw [sq_sqrt]; linarith 
          _ = (2 : ℝ) ^ 2 := by rw [this]
      nlinarith]
    <;> ring_nf <;> norm_num
    <;> ring
  have h2 : arctan (1 / (2 - sqrt 5)) = arctan (-(2 + sqrt 5)) := by rw [h1]
  have h3 : arctan (-(2 + sqrt 5)) = - arctan (2 + sqrt 5) := by
    rw [arctan_neg]
  rw [h2, h3]
  have h4 : 0 < 5 * sqrt 7 / 4 := by
    have : 0 < sqrt 7 := Real.sqrt_pos.2 (by norm_num)
    linarith
  linarith