import Mathlib

theorem algebra_139146 (x y z w : ℝ)
    (h1 : (x + y + z) / 3 = 14) (h2 : x + y + z + w = 50)
    (h3 : z = 4) (h4 : w = z / 5) :
    y = 20 ∧ w = 8 := by

  have h5 : x + y + z = 42 := by
    linarith
  have h6 : x + y = 38 := by
    rw [h3] at h5
    linarith
  have h7 : x + y + w = 46 := by
    rw [h3] at h2
    linarith
  have h8 : w = 8 := by
    linarith [h6, h7]
  have h9 : w = (4 : ℝ) / 5 := by
    rw [h3] at h4
    linarith
  -- We have a contradiction since w cannot be both 8 and 4/5.
  have h10 : (8 : ℝ) = (4 / 5 : ℝ) := by
    linarith [h8, h9]
  -- This is a contradiction, so we can derive anything.
  exfalso
  linarith