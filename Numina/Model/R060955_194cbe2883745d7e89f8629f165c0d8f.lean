import Mathlib

theorem algebra_95052 {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ x > 0, a / (10 ^ x - 1) + b / (10 ^ x + 2) = (2 * 10 ^ x + 3) / ((10 ^ x - 1) * (10 ^ x + 2))) :
    a - b = 4 / 3 := by
  have eq1 := h 1 (by norm_num)
  have eq2 := h 2 (by norm_num)
  norm_num at eq1 eq2
  linarith