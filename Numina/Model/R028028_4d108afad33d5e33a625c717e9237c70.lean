import Mathlib

theorem algebra_42492 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (hxy : x = 1 / (y ^ 2 + y - 1)) (hyz : y = 1 / (z ^ 2 + z - 1)) (hzx : z = 1 / (x ^ 2 + x - 1)) :
    (x, y, z) = (1, 1, 1) := by
  have eq1 : x * (y ^ 2 + y - 1) = 1 := by
    field_simp [(show y ^ 2 + y - 1 ≠ 0 by
      by_contra h
      have : x = 0 := by
        field_simp [h] at hxy 
        linarith
      linarith
    )] at hxy
    linarith
  have eq2 : y * (z ^ 2 + z - 1) = 1 := by
    field_simp [(show z ^ 2 + z - 1 ≠ 0 by
      by_contra h
      have : y = 0 := by
        field_simp [h] at hyz 
        linarith
      linarith
    )] at hyz
    linarith
  have eq3 : z * (x ^ 2 + x - 1) = 1 := by
    field_simp [(show x ^ 2 + x - 1 ≠ 0 by
      by_contra h
      have : z = 0 := by
        field_simp [h] at hzx 
        linarith
      linarith
    )] at hzx 
    linarith
  have h1 : x = 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]
  have h2 : y = 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]
  have h3 : z = 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]
  simp [h1, h2, h3]