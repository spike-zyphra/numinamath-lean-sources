import Mathlib

theorem algebra_312786 {x : ℝ} (hx : x = (1 + Real.sqrt 1994) / 2) :
    (4 * x ^ 3 - 1997 * x - 1994) ^ 2001 = -1 := by
  have h1 : 4 * x ^ 2 = 4 * x + 1993 := by
    have hx2 : 2 * x - 1 = Real.sqrt 1994 := by
      rw [hx]
      ring
    have : (2 * x - 1) ^ 2 = 1994 := by
      rw [hx2]
      exact Real.sq_sqrt (by norm_num)
    linarith
  have h2 : 4 * x ^ 3 - 1997 * x - 1994 = -1 := by
    have h2 : 4 * x ^ 3 = x * (4 * x + 1993) := by
      calc
        4 * x ^ 3 = x * (4 * x ^ 2) := by ring
        _ = x * (4 * x + 1993) := by rw [h1]
    calc
      4 * x ^ 3 - 1997 * x - 1994 = x * (4 * x + 1993) - 1997 * x - 1994 := by rw [h2]
      _ = 4 * x ^ 2 + 1993 * x - 1997 * x - 1994 := by ring
      _ = 4 * x + 1993 + 1993 * x - 1997 * x - 1994 := by rw [h1]
      _ = -1 := by ring
  rw [h2]
  norm_num