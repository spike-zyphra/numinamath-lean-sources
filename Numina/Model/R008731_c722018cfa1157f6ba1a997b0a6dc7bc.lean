import Mathlib 

theorem Algebra_611547 {x y z: ℝ} (hx : x > 0) (hy : 0 < y) (hz : 0 < z) 
  (h1 : x + y + z = 27) (h2 : x ^ 2 + y ^ 2 + z ^ 2 -x * y- y * z - z * x = 0) 
  : x = 9 ∧ y = 9 ∧ z = 9 := by 
  have h : (x - y)^2 + (y - z)^2 + (z - x)^2 = 0 := by 
    nlinarith 
  have hxy : (x - y) ^ 2 ≥ 0 := by 
    exact sq_nonneg (x - y)
  have hyz : (y - z) ^ 2 ≥ 0 := by 
    exact sq_nonneg (y - z)
  have hzx : (z - x) ^ 2 ≥ 0 := by 
    exact sq_nonneg (z - x)
  have hxy' : (x - y) ^ 2 = 0 := by 
    nlinarith [h, hxy, hyz, hzx]
  have hyz' : (y - z) ^ 2 = 0 := by 
    nlinarith [h, hxy, hyz, hzx]
  have hzx' : (z - x) ^ 2 = 0 := by 
    nlinarith [h, hxy, hyz, hzx]
  have hxy_eq : x = y := by 
    have hxy_zero : (x - y) = 0 := by 
      rw [sq_eq_zero_iff] at hxy'
      linarith 
    linarith 
  have hyz_eq : y = z := by 
    have hyz_zero : (y - z) = 0 := by 
      rw [sq_eq_zero_iff] at hyz'
      linarith 
    linarith 
  have hx_eq : x = 9 := by 
    nlinarith [hxy_eq, hyz_eq, h1] 
  have hy_eq : y = 9 := by 
    linarith [hx_eq, hxy_eq] 
  have hz_eq : z = 9 := by 
    linarith [hy_eq, hyz_eq] 
  exact ⟨hx_eq, hy_eq, hz_eq⟩