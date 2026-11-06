import Mathlib

theorem algebra_7431 {x y z : ℝ} (h1 : x + y + z = 15) (h2 : x * y + y * z + z * x = 72) :
  3 ≤ x ∧ x ≤ 7 := by
    have h3 : y + z = 15 - x := by
      linarith 
    have h4 : x * (y + z) + y * z = 72 := by 
      nlinarith [h2]
    have h5 : x * (y + z) = x * (15 - x) := by 
      rw [show y + z = 15 - x by linarith [h3]]
    rw [h5] at h4
    have h6 : y * z = x^2 - 15 * x + 72 := by 
      nlinarith [h4, h1, h3]
    have h7 : (y - z)^2 ≥ 0 := by 
      apply sq_nonneg
    have h8 : (y + z)^2 - 4 * (y * z) ≥ 0 := by 
      nlinarith [h7]
    rw [show (y + z) = 15 - x by linarith [h3]] at h8
    rw [show y * z = x^2 - 15 * x + 72 by linarith [h6]] at h8
    constructor
    · -- Proof that 3 ≤ x 
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 7)]
    · -- Proof that x ≤ 7 
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 7)]