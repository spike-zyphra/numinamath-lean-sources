import Mathlib

theorem algebra_120988 {x y z : ℝ} (h1 : x + y + z = 3) (h2 : x^2 + y^2 + z^2 = 3) (h3 : x^3 + y^3 + z^3 = 3) :
    (x, y, z) = (1, 1, 1) := by
  have h4 : x * y + y * z + z * x = 3 := by
    have eq1 : x^2 + y^2 + z^2 = (x + y + z)^2 - 2 * (x * y + y * z + z * x) := by ring
    rw [h1] at eq1
    linarith [h2, eq1]
  have h5 : x * y * z = 1 := by
    have eq1 : x^3 + y^3 + z^3 - 3 * (x * y * z) = (x + y + z) * ((x^2 + y^2 + z^2) - (x * y + y * z + z * x)) := by ring
    rw [h1, h2, h4] at eq1
    linarith [h3, eq1]
  have hx1 : x = 1 := by
    have h6 : (x - 1)^2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        h1, h4, h5]
    have : x - 1 = 0 := by
      nlinarith [sq_nonneg (x - 1), h6]
    linarith
  have hy1 : y = 1 := by
    have h6 : (y - 1)^2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        h1, h4, h5]
    have : y - 1 = 0 := by
      nlinarith [sq_nonneg (y - 1), h6]
    linarith
  have hz1 : z = 1 := by
    have h6 : (z - 1)^2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        h1, h4, h5]
    have : z - 1 = 0 := by
      nlinarith [sq_nonneg (z - 1), h6]
    linarith
  simp [hx1, hy1, hz1]