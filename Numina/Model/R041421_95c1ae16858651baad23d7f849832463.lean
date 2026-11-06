import Mathlib

theorem algebra_67551 {x y z : ℝ} (h1 : x + y + z = 2) (h2 : (x + y) * (y + z) + (y + z) * (z + x) + (z + x) * (x + y) = 1) (h3 : x ^ 2 * (y + z) + y ^ 2 * (z + x) + z ^ 2 * (x + y) = -6) :
    (x, y, z) = (0, 3, -1) ∨ (x, y, z) = (0, -1, 3) ∨ (x, y, z) = (3, 0, -1) ∨ (x, y, z) = (3, -1, 0) ∨ (x, y, z) = (-1, 0, 3) ∨ (x, y, z) = (-1, 3, 0) := by

  have h4 : z = 2 - x - y := by linarith
  rw [show z = 2 - x - y by linarith [h1]] at h2 h3

  have h5 : (x - 0) * (x - 3) * (x - (-1)) = 0 := by
    nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 3), sq_nonneg (x - (-1)), sq_nonneg (y - 3), sq_nonneg (y - (-1)), sq_nonneg (y - 0)]

  cases' (mul_eq_zero.mp h5) with h6 h7
  cases' (mul_eq_zero.mp h6) with h8 h9

  · -- x = 0
    have hx : x = 0 := by linarith
    have h_eq1 : y ^ 2 * (2 - y) + (2 - y) ^ 2 * y = -6 := by 
      rw [hx] at h3
      nlinarith 
    have h_eq2 : (y - 3) * (y + 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
    · -- y = 3
      have hy : y = 3 := by linarith
      have hz : z = -1 := by 
        nlinarith [hx]
      simp [hx, hy, hz]
    · -- y = -1
      have hy : y = -1 := by linarith
      have hz : z = 3 := by
        nlinarith [hx]
      simp [hx, hy, hz]

  · -- x = 3
    have hx : x = 3 := by linarith 
    have h_eq1 : 7 * y * (y + 1) = 0 := by
      rw [hx] at h3
      nlinarith 
    cases' (mul_eq_zero.mp h_eq1) with h_eq3 h_eq4 
    · -- 7 * y = 0, so y = 0
      have hy : y = 0 := by linarith 
      have hz : z = -1 := by 
        nlinarith [hx]
      simp [hx, hy, hz]
    · -- y + 1 = 0, so y = -1
      have hy : y = -1 := by linarith 
      have hz : z = 0 := by 
        nlinarith [hx]
      simp [hx, hy, hz]

  · -- x = -1 
    have hx : x = -1 := by linarith 
    have h_eq1 : 5 * y * (3 - y) = 0 := by 
      rw [hx] at h2 h3 
      nlinarith 
    cases' (mul_eq_zero.mp h_eq1) with h_eq3 h_eq4 
    · -- 5 * y = 0, so y = 0 
      have hy : y = 0 := by linarith 
      have hz : z = 3 := by 
        nlinarith [hx]
      simp [hx, hy, hz]
    · -- 3 - y = 0, so y = 3 
      have hy : y = 3 := by linarith 
      have hz : z = 0 := by 
        nlinarith [hx]
      simp [hx, hy, hz]