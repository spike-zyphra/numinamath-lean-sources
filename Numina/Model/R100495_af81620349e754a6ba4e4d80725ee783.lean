import Mathlib

theorem algebra_285558 {g s : ℝ} (hg : g > 0) (hs : s > 0)
    (h1 : g + s = 100) (h2 : (1 / 5) * g + (1 / 7) * s = (1 / 7) * g) :
    (1 / 7) * s = (9 / 49) * s := by 
  have h3 : 2 * g + 5 * s = 0 := by
    linarith
  
  -- From h1: g + s = 100
  -- Solving the system of equations leads to s < 0, which contradicts hs: s > 0
  have h4 : s < 0 := by
    have eq1 : g + s = 100 := h1
    have eq2 : 2 * g + 5 * s = 0 := h3
    linarith
  
  -- This contradicts the assumption hs: s > 0
  linarith [hs, h4]