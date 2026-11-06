import Mathlib

theorem algebra_283687 {x y : ℕ} (hx : x = 10 * y) (hy : y ≠ 0)
    (h : x * 45 = y * 10) : y = 10 := by
  rw [hx] at h
  -- The equation now becomes (10*y) * 45 = y*10
  -- Therefore, 450*y = 10*y
  -- Subtracting 10*y gives 440*y = 0
  have h1 : 440 * y = 0 := by 
    omega
  -- From 440*y = 0, we get y = 0
  have h2 : y = 0 := by
    omega
  -- Contradiction with the hypothesis y ≠ 0
  contradiction