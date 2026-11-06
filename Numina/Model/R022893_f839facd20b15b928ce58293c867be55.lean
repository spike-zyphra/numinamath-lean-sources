import Mathlib

theorem algebra_118819 (x y z : ℚ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 2) :
    1 / x + y + z + 2 = (y + 2) * (z + 2) / 2 ∧
    ∃ q : ℚ, Real.sqrt (2 * (1 / x + y + z + 2) * (1 / y + z + x + 2) * (1 / z + x + y + 2)) = q := by 
  constructor
  · -- Prove the first part of the theorem
    have h1 : x ≠ 0 := by
      linarith
    have h2 : 1 / x = y * z / 2 := by
      field_simp [(show x ≠ 0 by linarith)]
      nlinarith [hxyz]
    rw [h2]
    have eq1 : y * z / 2 + y + z + 2 = (y + 2) * (z + 2) / 2 := by
      ring_nf
    linarith [eq1]
  · -- Prove the second part of the theorem
    have h3 : (1 / x + y + z + 2) = (y + 2) * (z + 2) / 2 := by
      -- copy from above
      have h1 : x ≠ 0 := by
        linarith
      have h2 : 1 / x = y * z / 2 := by
        field_simp [(show x ≠ 0 by linarith)]
        nlinarith [hxyz]
      rw [h2]
      have eq1 : y * z / 2 + y + z + 2 = (y + 2) * (z + 2) / 2 := by
        ring_nf
      linarith [eq1]
    have h4 : (1 / y + z + x + 2) = (z + 2) * (x + 2) / 2 := by
      have h1 : y ≠ 0 := by
        linarith
      have h2 : 1 / y = z * x / 2 := by
        field_simp [(show y ≠ 0 by linarith)]
        nlinarith [show x * y * z = 2 by linarith, hxyz]
      rw [h2]
      have eq1 : z * x / 2 + z + x + 2 = (z + 2) * (x + 2) / 2 := by
        ring_nf
      linarith [eq1]
    have h5 : (1 / z + x + y + 2) = (x + 2) * (y + 2) / 2 := by
      have h1 : z ≠ 0 := by
        linarith
      have h2 : 1 / z = x * y / 2 := by
        field_simp [(show z ≠ 0 by linarith)]
        nlinarith [show x * y * z = 2 by linarith, hxyz]
      rw [h2]
      have eq1 : x * y / 2 + x + y + 2 = (x + 2) * (y + 2) / 2 := by
        ring_nf
      linarith [eq1]
    use ( (x + 2) * (y + 2) * (z + 2) / 2 )
    have h6 : (2 * (1 / x + y + z + 2) * (1 / y + z + x + 2) * (1 / z + x + y + 2) : ℝ) = ((x + 2) * (y + 2) * (z + 2) / 2 ) ^ 2 := by 
      have eq1 : (1 / x + y + z + 2 : ℝ) = ( (y + 2) * (z + 2) / 2 ) := by 
        exact_mod_cast h3
      have eq2 : (1 / y + z + x + 2 : ℝ) = ( (z + 2) * (x + 2) / 2 ) := by 
        exact_mod_cast h4
      have eq3 : (1 / z + x + y + 2 : ℝ) = ( (x + 2) * (y + 2) / 2 ) := by 
        exact_mod_cast h5
      rw [eq1, eq2, eq3]
      field_simp
      <;> ring_nf
    rw [h6]
    have h7 : (Real.sqrt (( (x + 2) * (y + 2) * (z + 2) / 2 ) ^ 2 ) : ℝ) = ( (x + 2) * (y + 2) * (z + 2) / 2 ) := by
      rw [Real.sqrt_sq (by 
        -- Positive since x + 2 > 0, y + 2 > 0, z + 2 > 0
        have h1 : (0 : ℝ) < x + 2 := by exact_mod_cast show 0 < x + 2 from by linarith
        have h2 : (0 : ℝ) < y + 2 := by exact_mod_cast show 0 < y + 2 from by linarith
        have h3 : (0 : ℝ) < z + 2 := by exact_mod_cast show 0 < z + 2 from by linarith
        positivity
      )]
      all_goals nlinarith
    exact_mod_cast h7