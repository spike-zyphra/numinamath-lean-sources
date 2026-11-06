import Mathlib

theorem inequalities_199368 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (0 < (a + b + c)^2 - 8 * a * c) ∨ (0 < (a + b + c)^2 - 8 * b * c) ∨
    (0 < (a + b + c)^2 - 8 * a * b) := by
  by_contra h
  push_neg at h
  -- now h means none of them is positive
  -- Now we show that sum of them is positive, thus a contradiction.
  -- Sum them up:
  --[(a + b + c)^2 - 8 * a * c] + [(a + b + c)^2 - 8 * b * c] + [(a + b + c)^2 - 8 * a * b] = 3 * (a + b + c)^2 - 8 * a * b - 8 * b * c - 8 * a * c
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]