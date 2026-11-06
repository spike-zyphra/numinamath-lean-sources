import Mathlib

theorem algebra_95870 (z1 z2 y1 y2:ℝ)
(h1 : (z1 + 3) = y1)
(h2 : (y1 + 18) = y2)
(h3: z2 + 3 = y2)
(h4: z1 + 18 = z2)
: y1 + y2 ≠ z1 + z2 + 22 := by
  intro h
  have eq5 : z1 = y1 - 3 := by linarith
  have eq6 : z2 = z1 + 18 := by linarith
  have eq7 : z2 = y1 + 15 := by
    rw [eq5] at eq6
    linarith
  have eq8 : y1 + y2 = z1 + z2 + 22 := by linarith [h]
  have eq9 : y2 = y1 + 34 := by
    rw [eq5, eq7] at eq8
    linarith
  have eq10 : y2 = y1 + 18 := by linarith [h2]
  linarith [eq9, eq10]