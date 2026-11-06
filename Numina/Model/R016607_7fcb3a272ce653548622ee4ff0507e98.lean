import Mathlib

theorem algebra_142361 (x y z : ℝ) (h₀ : 3 * x + y - z - 6 = 0) (h₁ : 3 * x - y + 2 * z = 0) :
    (x - 1) / (1 : ℝ) = (y - 3) / (-9 : ℝ) ∧ (y - 3) / (-9 : ℝ) = z / (-6 : ℝ) := by
  constructor
  · -- Prove the first equality: (x - 1) / 1 = (y - 3) / (-9)
    field_simp
    linarith
  · -- Prove the second equality: (y - 3) / (-9) = z / (-6)
    field_simp
    linarith