import Mathlib

theorem algebra_190620 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : (x * y + z) = (x + z) * (y + z)) :
    x * y * z ≤ 1 / 27 := by
  have h1 : x + y + z = 1 := by 
    have eq1 : z = x * z + y * z + z^2 := by
      nlinarith
    have h2 : z > 0 := hz
    have h3 : z * (x + y + z - 1) = 0 := by
      nlinarith
    have h4 : x + y + z - 1 = 0 := by
      apply_fun (fun w => w / z) at h3
      field_simp [hz.ne.symm] at h3 ⊢
      linarith
    linarith
  nlinarith [sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg (z - 1/3), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          h1]