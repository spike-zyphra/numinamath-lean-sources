import Mathlib

theorem algebra_321444 (x : ℝ) :
    (x + 1) * (x + 2) * (x + 3) * (x + 6) - 3 * x^2 =
    (x^2 + 4 * x + 6) * (x + 4 - Real.sqrt 10) * (x + 4 + Real.sqrt 10) := by 
  have h1 : (Real.sqrt 10) ^ 2 = 10 := by
    rw [Real.sq_sqrt]
    norm_num
  -- Compute (x + 4 - sqrt 10)(x + 4 + sqrt 10) = (x + 4)^2 - 10
  have h3 : (x + 4 - Real.sqrt 10) * (x + 4 + Real.sqrt 10) = (x + 4) ^ 2 - 10 := by
    nlinarith [Real.sqrt_nonneg 10, h1]
  calc
    (x + 1) * (x + 2) * (x + 3) * (x + 6) - 3 * x^2
        = (x^2 + 4 * x + 6) * ((x + 4) ^ 2 - 10) := by
          ring_nf
    _ = (x^2 + 4 * x + 6) * (x + 4 - Real.sqrt 10) * (x + 4 + Real.sqrt 10) := by
      rw [show (x^2 + 4 * x + 6) * ((x + 4) ^ 2 - 10) = (x^2 + 4 * x + 6) * ((x + 4 - Real.sqrt 10) * (x + 4 + Real.sqrt 10)) by 
        rw [h3]
      ]
      <;> ring