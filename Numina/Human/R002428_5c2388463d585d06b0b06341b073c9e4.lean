import Mathlib
open Real
/-John ordered 4 pairs of black socks and some additional pairs of blue socks. The price of the black socks per pair was
twice that of the blue. When the order was filled, it was found that the number of pairs of the two colors had been
interchanged. This increased the bill by 50%. The ratio of the number of pairs of black socks to the number of pairs of
blue socks in the original order was:
(A) 4 : 1 (B) 2 : 1 (C) 1 : 4 (D) 1 : 2 (E) 1 : 8
-/
theorem algebra_93209 {black pblack blue pblue : ℕ}
  (hblack : black = 4)
  (hn1 : black ≠ 0) (hn2 : blue ≠ 0)
  (hp1 : pblack ≠ 0) (hp2 : pblue ≠ 0)
  (hp : pblack = 2 * pblue)
  (h : (3:ℚ)/2*(black*pblack+blue*pblue) = blue*pblack+black*pblue) :
(black:ℚ) / blue = 1 / 4 := by
  -- getting rid of the divisions in the main equation
  field_simp at *
  norm_cast at *
  -- eliminate pblack and pblue in the equation
  rw [hp] at h
  have h':3 * (black * 2 + blue)*pblue = (blue * 2 + black) * 2 * pblue := by linarith
  simp [hp2] at h'
  -- solve the equation to obtain the answer
  linarith