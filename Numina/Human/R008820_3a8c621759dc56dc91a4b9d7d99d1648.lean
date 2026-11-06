import Mathlib

/- Let $p$ and $q$ be the two distinct solutions to the equation $$(x-5)(2x+9) = x^2-13x+40.$$What is $(p + 3)(q + 3)$? -/
theorem algebra_10239 {p q : ℝ} (hp : p ≠ q) (h : (p - 5) * (2 * p + 9) = p ^ 2 - 13 * p + 40)
    (hq : (q - 5) * (2 * q + 9) = q ^ 2 - 13 * q + 40) :
    (p + 3) * (q + 3) = -112 := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr hp)
  nlinarith