import Mathlib

theorem algebra_131897 {x y z : ℝ} (h1 : x + y + 2 * z = 0) (h2 : x * y - z ^ 2 = 0)
    (h3 : y ^ 2 + 5 * z + 6 = 0) :
    (x, y, z) = (2, 2, -2) ∨ (x, y, z) = (3, 3, -3) := by
  have h5 : x = -z := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 2 * z), sq_nonneg (x + z), sq_nonneg (y + z)]
  have h6 : y = -z := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 2 * z), sq_nonneg (x + z), sq_nonneg (y + z)]
  have hquadratic : z ^ 2 + 5 * z + 6 = 0 := by
    rw [show y = -z by linarith [h6]] at h3
    nlinarith
  have hquadraticfactors : (z + 2) * (z + 3) = 0 := by
    nlinarith [hquadratic]
  cases' (mul_eq_zero.1 hquadraticfactors) with hz2 hz3
  · -- Case z = -2 from $z + 2 = 0$
    have hz1 : z = -2 := by linarith
    have hx1 : x = 2 := by 
      linarith [hz1, h5]
    have hy1 : y = 2 := by 
      linarith [hz1, h6]
    left
    simp [hx1, hy1, hz1]
  · -- Case z = -3 from $z + 3 = 0$
    have hz2 : z = -3 := by linarith
    have hx2 : x = 3 := by
      linarith [hz2, h5]
    have hy2 : y = 3 := by
      linarith [hz2, h6]
    right
    simp [hx2, hy2, hz2]