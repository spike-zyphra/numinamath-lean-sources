import Mathlib

theorem inequalities_721 (x y z : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hyz : y < z)
    (hzx : z ≤ 4 * x) :
    y * z + z * x - x * y ≤ (x ^ 2 + y ^ 2 + z ^ 2) / 2 ∧
    (y * z + z * x - x * y = (x ^ 2 + y ^ 2 + z ^ 2) / 2 ↔ x + y = z) := by
  constructor
  · -- Prove the inequality \( y * z + z * x - x * y \leqslant (X ^ 2 + y ^ 2 + z ^ 2) / 2 \)
    suffices 0 ≤ (x + y - z) ^ 2 by
      linarith
    apply sq_nonneg
  · -- Prove the equality condition
    constructor
    · -- Assume \( y * z + z * x - x * y = (x ^ 2 + y ^ 2 + z ^ 2) / 2 \), then \( x + y = z \)
      intro h_eq
      have h_eq2 : (x + y - z) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x + y - z)]
      have h_eq3 : x + y - z = 0 := by
        rw [sq_eq_zero_iff] at h_eq2
        exact h_eq2
      linarith
    · -- Assume \( x + y = z \), then \( y * z + z * x - x * y = (X ^ 2 + y ^ 2 + z ^ 2) / 2 \)
      intro h_eq
      have hz : z = x + y := by linarith
      rw [hz]
      nlinarith