import Mathlib

theorem algebra_1057 (a b c d : ℝ)
  (h1 : a ≠ 0)
  (h2 : a + b + c + d = 1)
  (h3 : 8*a + 4*b + 2*c + d = 1/2)
  (h4 : 27*a + 9*b + 3*c + d = 1/3)
  (h5 : 64*a + 16*b + 4*c + d = 1/4)
: a + b = 3/8 ∧ c + d = 5/8 := by
  have eq5 : 7 * a + 3 * b + c = -1 / 2 := by 
    linarith
  have eq6 : 19 * a + 5 * b + c = -1 / 6 := by
    linarith
  have eq7 : 37 * a + 7 * b + c = -1 / 12 := by
    linarith

  have eq8 : 12 * a + 2 * b = 1 / 3 := by 
    linarith [eq5, eq6]

  have eq9 : 18 * a + 2 * b = 1 / 12 := by
    linarith [eq6, eq7]

  have ha : a = -1 / 24 := by 
    linarith [eq8, eq9]

  have hb : b = 5 / 12 := by 
    linarith [eq8, ha]

  have hc : c = -35 / 24 := by 
    linarith [eq5, ha, hb]

  have hd : d = 25 / 12 := by 
    linarith [h2, ha, hb, hc]

  constructor
  · -- Prove a + b = 3/8
    linarith [ha, hb]
  · -- Prove c + d = 5/8
    linarith [hc, hd]