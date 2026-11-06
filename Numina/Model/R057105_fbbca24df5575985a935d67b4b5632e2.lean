import Mathlib

theorem algebra_1431
  {x : ℝ}
  (hx : 3 * x^2 + x - 1 = 0) :
  6 * x^3 - x^2 - 3 * x + 2010 = 2009 := by
    have h1 : x^2 = -1/3 * x + 1/3 := by
      linarith [hx]

    have h2 : x^3 = 4/9 * x - 1/9 := by
      calc
        x^3 = x * x^2 := by ring
        _ = x * (-1/3 * x + 1/3) := by rw [h1]
        _ = -1/3 * x^2 + 1/3 * x := by ring
        _ = -1/3 * (-1/3 * x + 1/3) + 1/3 * x := by rw [h1]
        _ = 4/9 * x - 1/9 := by ring

    have h3 : 6 * x^3 = 8/3 * x - 2/3 := by 
      rw [h2]
      ring

    have h4 : -x^2 = 1/3 * x - 1/3 := by 
      rw [h1]
      ring

    linarith [h3, h4, hx]