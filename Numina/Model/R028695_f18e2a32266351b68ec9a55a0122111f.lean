import Mathlib

theorem algebra_157655 (p q : ℝ) (hp : p = 0.2) (hq : q = 0.3) :
    p * q = 0.06 ∧ (1 - p) * (1 - q) = 0.56 := by
  constructor
  · -- First, prove that p * q = 0.06
    rw [hp, hq]
    norm_num
  · -- Now, prove that (1 - p) * (1 - q) = 0.56
    rw [hp, hq]
    norm_num