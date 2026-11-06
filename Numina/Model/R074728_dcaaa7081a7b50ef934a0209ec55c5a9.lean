import Mathlib

theorem other_177928 (d1 d2 Dp Dc : ℝ) (hd1 : d1 = 5) (hd2 : d2 = 20)
    (hDp : Dp = -6) (hDc : Dc > 0) (h : d1 / Dp = d2 / Dc) :
    Dc = 10 := by
  rw [hd1, hDp, hd2] at h
  -- h becomes: 5 / (-6) = 20 / Dc
  have h1 : Dc ≠ 0 := by linarith
  field_simp [(show (-6 : ℝ) ≠ 0 by norm_num), h1] at h 
  nlinarith -- contradiction