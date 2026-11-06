import Mathlib

theorem algebra_310845 {a b c : ℝ} (ha : a > b) (hb : b > c)
    (hsum : a + b + c = 1) (hdiff : a^2 + b^2 + c^2 = 1) :
    a + b > 1 := by
  have h1 : c = 1 - (a + b) := by linarith
  by_contra h
  have h2 : c ≥ 0 := by linarith [h1, h]
  nlinarith [sq_pos_of_pos (sub_pos.mpr ha), sq_pos_of_pos (sub_pos.mpr hb), h1, h2, hsum, hdiff]