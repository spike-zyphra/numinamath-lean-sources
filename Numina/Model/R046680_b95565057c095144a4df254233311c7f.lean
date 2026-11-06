import Mathlib

theorem algebra_5653 (a b c : ℝ) (ha : 1 / a = 1 / b + 1 / 60) (hb : 1 / b = 1 / c + 375 / 1000)
    (hc : 1 / c = 1 / b + 30 / 60) :
    1 / c = 45 / 62 := by 
  have eq1 : 1 / b = 1 / c + 375 / 1000 := by linarith [hb]
  have eq2 : 1 / b = 1 / c - 30 / 60 := by 
    linarith [hc]
  -- From eq1 and eq2 deriving a contradiction
  -- Subtract eq2 from eq1: 0 = 375/1000 + 30/60
  -- i.e., -30/60 = 375/1000, which is -0.5 = 0.375, false.
  -- Thus the system is contradictory, so the theorem is vacuously true.
  -- We prove False to show the inconsistency
  have h5 : (375 / 1000 : ℝ) = (30 / 60 : ℝ) := by 
    nlinarith [eq1, eq2]
  nlinarith