import Mathlib

theorem algebra_194476 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x * 7 = y * 3) (h2 : x * 12 = y * 9) :
    x / y = 35 / 12 := by
  -- These hypotheses are inconsistent. Let's compute the contradiction.
  -- From h1: 7x = 3y => x = 3/7 y
  -- From h2: 12x = 9y => 4x = 3y => x = 3/4 y
  -- So 3/7 y = 3/4 y => y = 0, contradicting hy: y > 0.
  have h3 : y = 0 := by 
    nlinarith 
  -- Thus we get a contradiction
  linarith