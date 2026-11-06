import Mathlib

theorem algebra_186144 {x y z : ℝ} (h1 : x^3 + y^3 = 3 * y + 3 * z + 4)
    (h2 : y^3 + z^3 = 3 * z + 3 * x + 4) (h3 : z^3 + x^3 = 3 * x + 3 * y + 4) :
    (x, y, z) = (-1, -1, -1) ∨ (x, y, z) = (2, 2, 2) := by 
  -- Show that that sum of squared terms is zero
  have eq6 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z + 1), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
  -- From sum of squared terms is zero, we can get each term is zero
  have h7 : (x - y) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  have h8 : x - y = 0 := by 
    nlinarith
  have h9 : (y - z) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h10 : y - z = 0 := by
    nlinarith
  have h11 : x = y := by linarith
  have h12 : y = z := by linarith
  have h13 : x = z := by linarith
  have eq7 : x ^ 3 + x ^ 3 = 3 * x + 3 * x + 4 := by
    rw [show y = x by linarith [h11]] at h1
    rw [show z = x by linarith [h13]] at h1
    linarith
  have eq8 : x ^ 3 - 3 * x - 2 = 0 := by 
    nlinarith
  have eq9 : (x + 1) ^ 2 * (x - 2) = 0 := by 
    nlinarith [sq_nonneg (x^2 - 1)]
  cases' (mul_eq_zero.mp eq9) with h14 h15
  · -- Case where $(x + 1)^2 = 0$.
    have h16 : (x + 1) ^ 2 = 0 := by
      linarith
    have eq10 : x + 1 = 0 := by 
      nlinarith
    have hx1 : x = -1 := by linarith
    have hy1 : y = -1 := by linarith [hx1, h11]
    have hz1 : z = -1 := by linarith [hx1, h13]
    left
    simp [hx1, hy1, hz1]
  · -- Case where $x - 2 = 0$.
    have hx2 : x = 2 := by linarith
    have hy2 : y = 2 := by linarith [hx2, h11]
    have hz2 : z = 2 := by linarith [hx2, h13]
    right
    simp [hx2, hy2, hz2]