import Mathlib

theorem inequalities_38664 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 3) :
    3 / 2 < (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) ∧
    (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) < 3 := by

  have h10 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) < 3 := by
    have h1 : 0 < x + 2 := by linarith
    have h2 : 0 < y + 2 := by linarith
    have h3 : 0 < z + 2 := by linarith
    have h11 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 3 < 0 := by 
      have h4 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 3 =
          ( (1 + y^2) * (y + 2) * (z + 2) + (1 + z^2) * (x + 2) * (z + 2) + (1 + x^2) * (x + 2) * (y + 2) - 3 * (x + 2) * (y + 2) * (z + 2) ) / ( (x + 2) * (y + 2) * (z + 2) ) := by
        field_simp
        ring
      rw [h4] at *
      apply div_neg_of_neg_of_pos 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
        mul_pos (show 0 < x + 2 by linarith) (show 0 < y + 2 by linarith),
        mul_pos (show 0 < x + 2 by linarith) (show 0 < z + 2 by linarith),
        mul_pos (show 0 < y + 2 by linarith) (show 0 < z + 2 by linarith)]
      positivity 
    linarith
  have h12 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) > 3 / 2 := by
    have h13 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 3 / 2 > 0 := by 
      have h4 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 3 / 2 =
          ( (1 + y^2) * (y + 2) * (z + 2) + (1 + z^2) * (x + 2) * (z + 2) + (1 + x^2) * (x + 2) * (y + 2) - (3 / 2) * (x + 2) * (y + 2) * (z + 2) ) / ( (x + 2) * (y + 2) * (z + 2) ) := by
        field_simp
        ring
      rw [h4] at *
      apply div_pos
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
        mul_pos (show 0 < x + 2 by linarith) (show 0 < y + 2 by linarith),
        mul_pos (show 0 < x + 2 by linarith) (show 0 < z + 2 by linarith),
        mul_pos (show 0 < y + 2 by linarith) (show 0 < z + 2 by linarith)]
      positivity 
    linarith 
  constructor 
  · -- Prove that sum is greater than $3/2$
    linarith [h12]
  · -- Prove that sum is less than $3$
    linarith [h10]