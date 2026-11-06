import Mathlib

theorem algebra_199338 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 151/44 = 3 + 1/(x + 1/(y + 1/z : ℚ))) :
    x + y + z = 11 := by

  have h1 : (151 : ℚ) / (44 : ℚ) = 3 + 1 / (x + 1 / (y + 1 / z : ℚ)) := by 
    simpa using h
  have h2 : (151 : ℚ) / (44 : ℚ) - 3 = 1 / (x + 1 / (y + 1 / z : ℚ)) := by 
    linarith [h1]
  have h3 : (19 / (44 : ℚ) ) = 1 / (x + 1 / (y + 1 / z : ℚ)) := by
    norm_num at h2 ⊢
    linarith
  have h4 : (x + 1 / (y + 1 / z : ℚ) ) = (44 / 19 : ℚ) := by
    have h5 : (x + 1 / (y + 1 / z : ℚ) ) ≠ 0 := by
      have hx1 : (x : ℚ) > 0 := by exact_mod_cast hx
      have hy1 : (y : ℚ) > 0 := by exact_mod_cast hy
      have hz1 : (z : ℚ) > 0 := by exact_mod_cast hz
      have h_pos : (y + 1 / z : ℚ) > 0 := by
        have h1z : (z : ℚ) > 0 := hz1
        have h2z : 1 / (z : ℚ) > 0 := by 
          apply div_pos
          norm_num
          all_goals linarith
        linarith
      have h_pos2 : (x + 1 / (y + 1 / z : ℚ) : ℚ) > 0 := by
        have h1y : (x : ℚ) > 0 := hx1
        have h2y : 1 / (y + 1 / z : ℚ) > 0 := by
          apply div_pos
          norm_num
          all_goals linarith
        linarith
      linarith
    field_simp [h5] at h3 ⊢
    linarith

  have eq5 : x * 19 * (y * z + 1) + z * 19 = 44 * (y * z + 1) := by
    have eq1 : (x + 1 / (y + 1 / z : ℚ) ) = (44 / 19 : ℚ) := h4
    have eq2 : (x + 1 / (y + 1 / z : ℚ) ) = (x + (z / (y * z + 1 : ℚ)) ) := by
      field_simp [(show (z : ℚ) ≠ 0 by exact_mod_cast (show z ≠ 0 by omega)), 
        show (y : ℚ) ≠ 0 by exact_mod_cast (show y ≠ 0 by omega) ]
      <;> ring
    rw [eq2] at eq1
    have h5 : (x : ℚ) * 19 * ((y * z + 1) : ℚ) + (z : ℚ) * 19 = (44 * ((y * z + 1) : ℚ) ) := by 
      field_simp [(show ((y * z + 1 : ℚ) ) ≠ 0 by 
        have hy1 : (y : ℚ) > 0 := by exact_mod_cast hy
        have hz1 : (z : ℚ) > 0 := by exact_mod_cast hz
        nlinarith [sq_nonneg ((y : ℚ) ), sq_nonneg ((z : ℚ) ) ]
      ), (show (y : ℚ) ≠ 0 by exact_mod_cast (show y ≠ 0 by omega) ), 
        (show (z : ℚ) ≠ 0 by exact_mod_cast (show z ≠ 0 by omega) )] at eq1 ⊢
      nlinarith
    exact_mod_cast h5

  -- solving the equation
  have hx2 : x = 2 := by
    have eq5' : x * 19 * (y * z + 1) + z * 19 = 44 * (y * z + 1) := eq5
    have h4 : x ≤ 2 := by
      nlinarith [ sq_nonneg ((x : ℤ) * (y * z + 1)), sq_nonneg ((y * z + 1 : ℤ)), sq_nonneg ((z : ℤ) ), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz ]
    have h5 : x ≥ 1 := by
      nlinarith
    interval_cases x <;> 
      try { 
        omega 
      }
      <;> try { 
            nlinarith 
      }
  -- Proving y=3
  have hy3 : y = 3 := by
    rw [show x = 2 by linarith [hx2] ] at eq5 
    -- This makes eq5: 2 * 19 * (y * z + 1) + 19 * z = 44 * (y * z + 1)
    have h6 : y = 3 := by
      nlinarith [ sq_nonneg ((y * z + 1 : ℤ) ), sq_nonneg ((z : ℤ) ), sq_nonneg ((y : ℤ) ), sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz ]
    exact_mod_cast h6
  -- Proving z=6
  have hz6 : z = 6 := by
    rw [show x = 2 by linarith [hx2] ] at eq5 
    rw [show y = 3 by linarith [hy3] ] at eq5 
    -- This makes eq5: 2 * 19 * (3 * 6 + 1) + 6 * 19 = 44 * (3 * 6 + 1)
    have h7 : z = 6 := by
      nlinarith [ sq_nonneg ((y * z + 1 : ℤ) ), sq_nonneg ((z : ℤ) ), sq_nonneg ((y : ℤ) ), sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz ]
    exact_mod_cast h7
  linarith [ show x = 2 from hx2, show y = 3 from hy3, show z = 6 from hz6 ]