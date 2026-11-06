import Mathlib

theorem algebra_15906 (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (h1 : a^2 + b^2 = 11) (h2 : c^2 + d^2 = 11)
    (h3 : (a - c)^2 + (b - d)^2 = 11) (h4 : (a - 3)^2 + (b + 2)^2 = 11)
    (h5 : (a - 8)^2 + (b - 4)^2 = 11) :
    2 * Real.sqrt 11 = 2 * Real.sqrt ((a - c)^2 + (b - d)^2) := by
  have h6 : (a - c) ^ 2 + (b - d) ^ 2 = 11 := h3
  have h8 : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 11 := by
    rw [h6]
  calc
    2 * Real.sqrt 11 = 2 * Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
      rw [h8]