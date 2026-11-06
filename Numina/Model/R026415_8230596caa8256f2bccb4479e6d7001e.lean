import Mathlib

theorem algebra_209052 {x y : ℝ} (hx : x ^ 4 + x ^ 3 - 1 = 0) (hy : y ^ 4 + y ^ 3 - 1 = 0)
    (hxy : x ≠ y) : (x * y) ^ 6 + (x * y) ^ 4 + (x * y) ^ 3 - (x * y) ^ 2 - 1 = 0 := by

  have h1 : x^4 = 1 - x^3 := by linarith
  have h2 : y^4 = 1 - y^3 := by linarith

  have h3 : x^5 = x - 1 + x^3 := by
    calc
      x^5 = x * x^4 := by ring
      _   = x * (1 - x^3) := by rw [h1]
      _   = x - x^4 := by ring
      _   = x - (1 - x^3) := by rw [h1]
      _   = x - 1 + x^3 := by ring

  have h4 : y^5 = y - 1 + y^3 := by
    calc
      y^5 = y * y^4 := by ring
      _   = y * (1 - y^3) := by rw [h2]
      _   = y - y^4 := by ring
      _   = y - (1 - y^3) := by rw [h2]
      _   = y - 1 + y^3 := by ring

  have h5 : x^6 = x^2 - x + 1 - x^3 := by
    calc
      x^6 = x * x^5 := by ring
      _   = x * (x - 1 + x^3) := by rw [h3]
      _   = x^2 - x + x^4 := by ring
      _   = x^2 - x + (1 - x^3) := by rw [h1]
      _   = x^2 - x + 1 - x^3 := by ring

  have h6 : y^6 = y^2 - y + 1 - y^3 := by
    calc
      y^6 = y * y^5 := by ring
      _   = y * (y - 1 + y^3) := by rw [h4]
      _   = y^2 - y + y^4 := by ring
      _   = y^2 - y + (1 - y^3) := by rw [h2]
      _   = y^2 - y + 1 - y^3 := by ring

  have h7 : (x * y) ^ 4 = (1 - x^3) * (1 - y^3) := by 
    calc 
      (x * y) ^ 4 = x^4 * y^4 := by ring 
      _ = (1 - x^3) * (1 - y^3) := by rw [h1, h2]

  have h8 : (x * y) ^ 6 = (x^2 - x + 1 - x^3) * (y^2 - y + 1 - y^3) := by 
    calc 
      (x * y) ^ 6 = x^6 * y^6 := by ring 
      _ = (x^2 - x + 1 - x^3) * (y^2 - y + 1 - y^3) := by rw [h5, h6]

  have h9 : (x * y) ^ 3 = x^3 * y^3 := by ring

  have h10 : (x * y) ^ 2 = x^2 * y^2 := by ring

  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hxy), hx, hy, h1, h2, h5, h6, h8, h7, h9, h10, h3, h4]