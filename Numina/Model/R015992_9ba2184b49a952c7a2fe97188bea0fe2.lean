import Mathlib

theorem inequalities_26286 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1 / x + 1 / y + 1 / z) : x * y + y * z + z * x ≥ 3 := by
  have h1 : 0 < x * y * z := by
    positivity
  have eq1 : 1 / x + 1 / y + 1 / z = (x * y + y * z + z * x) / (x * y * z) := by 
    field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
    <;> ring
  have eq2 : (x + y + z) * (x * y * z) = x * y + y * z + z * x := by 
    have h' : x + y + z = (x * y + y * z + z * x) / (x * y * z) := by
      linarith [eq1, h]
    have h4 : (x * y * z) > 0 := h1
    have : (x + y + z) * (x * y * z) = x * y + y * z + z * x := by
      calc
        (x + y + z) * (x * y * z) = ( (x * y + y * z + z * x) / (x * y * z) ) * (x * y * z) := by 
          rw [h']
        _ = x * y + y * z + z * x := by
          field_simp [h1]
          <;> ring
    linarith
  have h2 : (x * y + y * z + z * x) ≥ 3 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
      mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
      mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)]
  linarith [h2]