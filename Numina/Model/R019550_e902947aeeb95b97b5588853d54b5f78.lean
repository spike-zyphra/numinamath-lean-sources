import Mathlib

theorem algebra_249488 {x y z : ℝ} (hxyz : x * y * z = 1) :
    (x + 1 / x) ^ 2 + (y + 1 / y) ^ 2 + (z + 1 / z) ^ 2 -
    (x + 1 / x) * (y + 1 / y) * (z + 1 / z) = 4 := by
  have hx1 : x ≠ 0 := by 
    by_contra h
    have h1 : x * y * z = 0 := by 
      rw [h]
      norm_num 
    linarith
  have hy1 : y ≠ 0 := by 
    by_contra h
    have h1 : x * y * z = 0 := by 
      rw [h]
      norm_num 
    linarith 
  have hz1 : z ≠ 0 := by 
    by_contra h
    have h1 : x * y * z = 0 := by 
      rw [h]
      norm_num 
    linarith 
  have h5 : x^2 * y^2 * z^2 = 1 := by 
    have h6 : x * y * z = 1 := hxyz 
    calc 
      x^2 * y^2 * z^2 = (x * y * z) ^ 2 := by 
        ring 
      _ = 1 ^ 2 := by 
        rw [h6]
      _ = 1 := by 
        norm_num
  have h7 : (x + 1 / x) ^ 2 + (y + 1 / y) ^ 2 + (z + 1 / z) ^ 2 - (x + 1 / x) * (y + 1 / y) * (z + 1 / z) = 4 := by
    have h5' : x^2 * y^2 * z^2 = 1 := h5
    field_simp [hx1, hy1, hz1] at *
    <;> nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), 
            sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
            sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), 
            mul_nonneg (sq_nonneg (x * y)) (sq_nonneg (y * z)), 
            mul_nonneg (sq_nonneg (y * z)) (sq_nonneg (z * x)), 
            mul_nonneg (sq_nonneg (z * x)) (sq_nonneg (x * y)), 
            hxyz
          ]
  exact_mod_cast h7