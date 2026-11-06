import Mathlib

theorem algebra_192469 {x y z : ℝ} (h1 : 4 * x ^ 2 / (1 + 4 * x ^ 2) = y) (h2 : 4 * y ^ 2 / (1 + 4 * y ^ 2) = z) (h3 : 4 * z ^ 2 / (1 + 4 * z ^ 2) = x) :
    (x, y, z) = (0, 0, 0) ∨ (x, y, z) = (1 / 2, 1 / 2, 1 / 2) := by
  have eq1 : 4 * x ^ 2 = y * (1 + 4 * x ^ 2) := by
    have h1' : 1 + 4 * x ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg x]
    field_simp [h1'] at h1 ⊢
    <;> nlinarith
  have eq2 : 4 * y ^ 2 = z * (1 + 4 * y ^ 2) := by
    have h2' : 1 + 4 * y ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg y]
    field_simp [h2'] at h2 ⊢
    <;> nlinarith
  have eq3 : 4 * z ^ 2 = x * (1 + 4 * z ^ 2) := by
    have h3' : 1 + 4 * z ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg z]
    field_simp [h3'] at h3 ⊢
    <;> nlinarith
  have h5 : x * (x - 1 / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2),
      sq_nonneg (x * (y - 1 / 2)), sq_nonneg (y * (z - 1 / 2)), sq_nonneg (z * (x - 1 / 2))]
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- x = 0
    have hx : x = 0 := by linarith
    have hy : y = 0 := by
      rw [hx] at eq1
      nlinarith
    have hz : z = 0 := by
      rw [hy] at eq2
      nlinarith
    left
    simp [hx, hy, hz]
  · -- (x - 1/2) ^ 2 = 0
    have hx : x = 1 / 2 := by
      nlinarith
    have hy : y = 1 / 2 := by 
      rw [hx] at eq1
      nlinarith
    have hz : z = 1 / 2 := by 
      rw [hy] at eq2
      nlinarith
    right
    simp [hx, hy, hz]