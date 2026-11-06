import Mathlib

theorem other_172571 (H : ℝ) (hH : H > 0) (h : 0.9 * H = 1000 * x + 600 * y)
    (hx : x > 0) (hy : y > 0) (hxy : x + y = H) :
    x = 0.69 * H ∧ y = H := by
  have eq1 : y = H - x := by linarith
  rw [eq1] at h
  ring_nf at h 
  -- Let's solve the equations:
  -- 0.9 * H = 1000 * x + 600 * (H - x)
  -- 0.9 * H = 1000 * x + 600 * H - 600 * x
  -- 0.9 * H = 400 * x + 600 * H
  -- -599.1 * H = 400 * x
  -- x = -599.1 / 400 * H
  -- x = -1.4978 * H as H > 0
  -- This contradicts x > 0, the goal.
  nlinarith [hH]