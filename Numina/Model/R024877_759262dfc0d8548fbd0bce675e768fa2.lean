import Mathlib

open Real

theorem inequalities_171151 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    36 ≤ 1 / x + 4 / y + 9 / z := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h2 : 1 / x + 4 / y + 9 / z - 36 ≥ 0 := by
    have h3 : 1 / x + 4 / y + 9 / z - 36 = (y * z + 4 * x * z + 9 * x * y - 36 * x * y * z) / (x * y * z) := by 
      field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
      ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x - 1 / 6), sq_nonneg (y - 2 / 6), sq_nonneg (z - 3 / 6),
      hsum, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    positivity
  
  linarith