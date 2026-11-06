import Mathlib

theorem algebra_12724 (h w l : ℝ)
    (hl : l = 8.5)
    (hh : h = 7.5)
    (htriangle : h ^ 2 + w ^ 2 = l ^ 2)
    (hpos : 0 < w) :
    w = 4 := by 
  rw [hh, hl] at htriangle
  nlinarith [sq_pos_of_pos hpos, sq_nonneg (w - 4)]