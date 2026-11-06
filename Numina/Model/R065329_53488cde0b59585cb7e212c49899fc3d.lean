import Mathlib

theorem algebra_250656 (v : ℝ) (h : v > 0) (h1 : 3 * v + 1 * (v / 3) = 10) (h2 : 1 * v + 3 * (v / 3) = 15) :
    3 * v + 1 * (v / 3) = 60 := by 
  -- From h1: 3v + (v/3) = 10. Multiply by 3 to eliminate fraction:
  -- 9v + v = 30 => 10v = 30 => v = 3
  have h3 : v = 3 := by
    linarith
  
  -- From h2: v + 3*(v/3) = v + v = 2v = 15 => v = 7.5
  have h4 : v = 15 / 2 := by
    linarith
  
  -- v cannot be both 3 and 15/2 for the theorem to hold
  linarith -- Contradiction