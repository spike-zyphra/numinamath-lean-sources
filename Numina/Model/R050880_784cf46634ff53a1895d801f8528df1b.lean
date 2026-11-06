import Mathlib

theorem algebra_161457 {x y : ℝ} (h1 : 2*y - x - 2*x*y = -1) (h2 : 4*x^2*y^2 + x^2 + 4*y^2 - 4*x*y = 61) :
    (x = -6 ∧ y = -1/2) ∨ (x = 1 ∧ y = 3) ∨ (x = 1 ∧ y = -5/2) ∨ (x = 5 ∧ y = -1/2) := by
  have h4 : (1 + 2 * y) * (1 - x) = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y + 1/2)]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where 1 + 2*y = 0, so y = -1/2
    have hy : y = -1/2 := by linarith
    have : 2 * x^2 + 2 * x - 60 = 0 := by 
      rw [hy] at h2
      nlinarith 
    have h8 : (x - 5) * (x + 6) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h8) with hx1 hx2
    · -- Case where x = 5
      have hx5 : x = 5 := by linarith
      simp [hx5, hy, or_assoc]
    · -- Case where x = -6
      have hx6 : x = -6 := by linarith
      simp [hx6, hy]
  · -- Case where x = 1
    have hx1 : x = 1 := by linarith
    rw [hx1] at h2
    have h8 : 8 * y^2 - 4 * y - 60 = 0 := by 
      nlinarith [h2]
    have h5 : (y - 3) * (8 * y + 20) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h5) with hy1 hy2
    · -- Case where y = 3
      have hy3 : y = 3 := by linarith
      simp [hx1, hy3, or_assoc]
    · -- Case where y = -5/2
      have hy4 : y = -5/2 := by linarith
      simp [hx1, hy4, or_assoc]