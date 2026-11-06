import Mathlib

theorem inequalities_304473 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    x / (x ^ 2 + y ^ 3) + y / (x ^ 3 + y ^ 2) ≤
    2 * (x / (x + y ^ 2) + y / (x ^ 2 + y)) := by 
  have hy1 : y = 1 - x := by
    linarith
  rw [hy1]
  have hx1 : 0 < x := hx
  have hx2 : 0 < 1 - x := by
    have hy_eq : 1 - x = y := by
      linarith 
    rw [hy_eq]
    all_goals linarith
  have pos1 : 0 < x ^ 2 + (1 - x) ^ 3 := by
    positivity 
  have pos2 : 0 < x ^ 3 + (1 - x) ^ 2 := by
    positivity 
  have pos3 : 0 < x + (1 - x) ^ 2 := by 
    positivity 
  have pos4 : 0 < x ^ 2 + (1 - x) := by
    positivity 
  have h2 : x / (x ^ 2 + (1 - x) ^ 3) + (1 - x) / (x ^ 3 + (1 - x) ^ 2) - 2 * (x / (x + (1 - x) ^ 2) + (1 - x) / (x ^ 2 + (1 - x)) ) ≤ 0 := by 
    have h3 : 0 < (x ^ 2 + (1 - x) ^ 3) * (x ^ 3 + (1 - x) ^ 2) * (x + (1 - x) ^ 2) * (x ^ 2 + (1 - x)) := by 
      positivity 
    have h7 : x / (x ^ 2 + (1 - x) ^ 3) + (1 - x) / (x ^ 3 + (1 - x) ^ 2) - 2 * (x / (x + (1 - x) ^ 2) + (1 - x) / (x ^ 2 + (1 - x))) =
        (x * (x ^ 3 + (1 - x) ^ 2) * (x + (1 - x) ^ 2) * (x ^ 2 + (1 - x)) + 
          (1 - x) * (x ^ 2 + (1 - x) ^ 3) * (x + (1 - x) ^ 2) * (x ^ 2 + (1 - x)) - 
          2 * (x * (x ^ 2 + (1 - x) ^ 3) * (x ^ 3 + (1 - x) ^ 2) * (x ^ 2 + (1 - x)) + 
            (1 - x) * (x ^ 2 + (1 - x) ^ 3) * (x ^ 3 + (1 - x) ^ 2) * (x + (1 - x) ^ 2))
        ) / 
        ((x ^ 2 + (1 - x) ^ 3) * (x ^ 3 + (1 - x) ^ 2) * (x + (1 - x) ^ 2) * (x ^ 2 + (1 - x))) := by 
      field_simp 
      <;> ring 
    rw [h7] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- To prove the numerator is less than or equal to 0
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x * (x - 1 / 2)), sq_nonneg ((1 - x) * (x - 1 / 2)), sq_nonneg (x - (1 - x)), 
        sq_nonneg (x * (x - (1 - x))), sq_nonneg ((1 - x) * (x - (1 - x))), 
        mul_pos hx1 hx2, 
        mul_pos hx1 (show 0 < (1 - x) ^ 2 by positivity), 
        mul_pos hx2 (show 0 < x ^ 2 by positivity), 
        sq_nonneg (x ^ 2 - (1 - x) ^ 2), 
        sq_nonneg (x ^ 3 - (1 - x) ^ 3), 
        sq_nonneg (x * (x - (1 - x)) * (x + (1 - x))), 
        mul_pos (show 0 < x * (1 - x) by nlinarith) (show 0 < x * (1 - x) by nlinarith)
      ]
    · -- To prove the denominator is positive
      positivity
  linarith