import Mathlib

theorem algebra_202537 {x y z : ℝ} (h1 : 5732 * x + 2134 * y + 2134 * z = 7866)
    (h2 : 2134 * x + 5732 * y + 2134 * z = 670) (h3 : 2134 * x + 2134 * y + 5732 * z = 11464) :
    (x, y, z) = (1, -1, 2) := by
  have h4 : x + y + z = 2 := by
    linarith
  -- Substitute z = 2 - x - y into the third equation
  have h5 : x + y = 0 := by
    have eq3 := h3
    have hz : z = 2 - x - y := by linarith [h4]
    rw [hz] at eq3
    linarith
  -- From x + y = 0 and x + y + z = 2, we have z = 2
  have h6 : z = 2 := by
    linarith [h4, h5]
  -- From x + y = 0, we have y = -x
  have h7 : y = -x := by
    linarith
  -- Substitute y = -x and z = 2 into the first equation
  have h8 : x = 1 := by
    rw [h7, h6] at h1
    linarith
  -- From y = -x and x = 1, we get y = -1
  have h9 : y = -1 := by
    linarith [h7, h8]
  -- The solution is (1, -1, 2)
  have h10 : z = 2 := h6
  simp [Prod.ext_iff, h8, h9, h10]
  all_goals tauto