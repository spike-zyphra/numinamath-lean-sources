import Mathlib

theorem inequalities_603020 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    36 ≤ 1 / x + 4 / y + 9 / z := by

  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h2 : (1 / x + 4 / y + 9 / z) = (y * z + 4 * x * z + 9 * x * y) / (x * y * z) := by
    field_simp
    <;> ring

  have h3 : (y * z + 4 * x * z + 9 * x * y) ≥ 36 * (x * y * z) := by
    nlinarith [sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1 / 2), 
        sq_nonneg (x * y - 1 / 6 * 1 / 3), sq_nonneg (y * z - 1 / 3 * 1 / 2), sq_nonneg (z * x - 1 / 2 * 1 / 6), 
        hsum, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
      ]
  
  have h4 : (1 / x + 4 / y + 9 / z) ≥ 36 := by
    rw [h2]
    have h5 : (y * z + 4 * x * z + 9 * x * y) / (x * y * z) ≥ 36 := by
      apply (le_div_iff₀ (by linarith)).mpr
      linarith [h3]
    linarith [h5]

  linarith [h4]