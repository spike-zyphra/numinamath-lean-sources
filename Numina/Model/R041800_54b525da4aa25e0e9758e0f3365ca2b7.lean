import Mathlib

theorem algebra_132895 {x : ℝ} (hx : x ≠ 0) (h : (x^3 - 5 * x^2) / x^2 = (3 * x - 15) / 3) :
    ¬((x - 5) / 2 = x - 5 / 2) := by

  intro h1

  have eq3 : x = 0 := by
    norm_num at h1
    linarith

  -- x = 0 contradicts hx : x ≠ 0
  tauto