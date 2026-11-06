import Mathlib

theorem algebra_200074 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x + 1 / y = 4) (hyz : y + 1 / z = 1) (hzx : z + 1 / x = 7 / 3) :
    x * y * z = 1 := by
  have eq1 : x * y + 1 = 4 * y := by 
    have h1 : y ≠ 0 := hy
    field_simp at hxy
    linarith 
  have eq2 : y * z + 1 = z := by 
    have h2 : z ≠ 0 := hz
    field_simp at hyz 
    linarith
  by_cases hx0 : x = 0 
  · -- x = 0
    have h1 : z = 7 / 3 := by 
      rw [hx0] at hzx 
      field_simp at hzx 
      linarith 
    have h2 : y = 1 / 4 := by 
      rw [hx0] at eq1 
      nlinarith 
    rw [h2, h1] at eq2 
    norm_num at eq2 
  · -- x ≠ 0 
    have hx00 : x ≠ 0 := hx0 
    have eq3 : 3 * (z * x) = 7 * x - 3 := by 
      have h3 : x ≠ 0 := hx00 
      field_simp [hx00] at hzx ⊢ 
      linarith 
    -- Let's solve for z.
    -- From eq3: 3*z*x = 7*x - 3. 
    -- From eq1 : x * y + 1 = 4 * y
    -- From eq2 : y * z + 1 = z. 
    -- We can derive z from these equations, assuming x ≠0.
    -- Let's isolate the result first:
    -- From eq2: y * z = z - 1. Multiply by x: x*y*z = x*(z-1).
    -- From eq1: x*y = 4*y -1. Multiply by z: x*y*z = z*(4*y -1).
    -- So x*(z-1) = z*(4*y -1).
    -- Now combine with eq3.
    -- Let's instead solve directly for z = 5/3.
    have h4 : z = 5 / 3 := by 
      apply (mul_left_inj' hx00).mp 
      nlinarith [sq_pos_of_ne_zero hx00, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero hz, sq_nonneg (x * y - 1), sq_nonneg (y * z + 1), sq_nonneg (z * 3 - 7)]
    -- Now given z, compute final result.
    have hx01 : x * y * z = 1 := by 
      -- We need to express xyz in terms of z.
      have h5 : x * y * z = 3 * z - 4 := by 
        have h2 : y * z = z - 1 := by 
          linarith [eq2]
        have h1 : x * y = 4 * y - 1 := by 
          linarith [eq1]
        calc 
          x * y * z = (x * y) * z := by ring 
          _ = (4 * y - 1) * z := by rw [h1]
          _ = 4 * (y * z) - z := by ring
          _ = 4 * (z - 1) - z := by rw [h2]
          _ = 3 * z - 4 := by ring 
      rw [h5] 
      rw [h4] 
      norm_num 
    exact_mod_cast hx01