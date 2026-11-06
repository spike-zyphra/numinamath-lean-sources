import Mathlib

theorem algebra_134588 (x : ℝ) (hx : x = 2 - Real.sqrt 7) :
    x^2 - 4 * x - 3 = 0 := by
  rw [hx]
  have h1 : (2 - Real.sqrt 7) ^ 2 = 11 - 4 * Real.sqrt 7 := by
    calc
      (2 - Real.sqrt 7) ^ 2 = 2^2 - 2 * 2 * Real.sqrt 7 + (Real.sqrt 7) ^ 2 := by ring
      _ = 4 - 4 * Real.sqrt 7 + 7 := by norm_num [Real.sq_sqrt]
      _ = 11 - 4 * Real.sqrt 7 := by ring
  rw [h1]
  have h2 : 4 * (2 - Real.sqrt 7) = 8 - 4 * Real.sqrt 7 := by ring
  rw [h2]
  ring