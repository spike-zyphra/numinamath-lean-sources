import Mathlib

theorem algebra_2480 {x : ℝ} (hx : abs x = x + 2) : 19 * x^94 + 3 * x + 27 = 43:= by
  have h1 : x ≤ 0 := by
    by_contra h
    push_neg at h
    have h2 : abs x = x := by
      rw [abs_of_pos h]
    rw [h2] at hx
    linarith
  have h2 : abs x = -x := by
    rw [abs_of_nonpos (show x ≤ 0 by linarith)]
    all_goals linarith
  rw [h2] at hx
  have hx1 : x = -1 := by
    linarith
  rw [hx1]
  norm_num