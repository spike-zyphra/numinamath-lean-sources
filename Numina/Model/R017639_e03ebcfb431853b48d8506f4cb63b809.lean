import Mathlib

theorem algebra_146629 {x y z : ℝ} (h1 : (x + 1) * y * z = 12) (h2 : (y + 1) * z * x = 4) (h3 : (z + 1) * x * y = 4) :
    (x, y, z) = (2, -2, -2) ∨ (x, y, z) = (1 / 3, 3, 3) := by
  have eq1 : x * (z - y) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq1) with h4 h5
  · -- Case where x = 0, which leads to a contradiction.
    have h4' : x = 0 := by linarith
    rw [h4'] at h2
    nlinarith
  · -- Case where z = y.
    have h4' : z = y := by linarith
    rw [show z = y by linarith] at h1 h2 h3
    have h4 : (y - 3) * (y + 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 3), sq_nonneg (y + 2), sq_nonneg (x - 2), sq_nonneg (y + 2)]
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case where y = 3.
      have h4' : y = 3 := by linarith
      have h5' : x = 1 / 3 := by
        rw [h4'] at h2
        nlinarith
      simp [h5', h4', show z = 3 by linarith]
      <;> tauto
    · -- Case where y = -2.
      have h7 : y = -2 := by
        nlinarith [pow_eq_zero (show (y + 2) ^ 2 = 0 by linarith)]
      have h8 : x = 2 := by
        rw [h7] at h2
        nlinarith
      simp [h8, h7, show z = -2 by linarith]
      <;> tauto