import Mathlib
import Mathlib.Tactic.NormNum

/--
Menkara has a 4 × 6 index card. If she shortens the length of one side by 1 inch,
the card would have area 18 square inches. What would the area of the card be in
square inches if instead she shortens the length of the other side by 1 inch?

(A) 16
(B) 17
(C) 18
(D) 19
(E) 20
-/

theorem algebra_93067 {x y : ℝ} (hx : x = 4) (hy : y = 6):
  x * (y - 1) = 20 := by
    -- We substitute x=4 and y=6 into x*(y-1) since with such values we get (x-1)*y=18.
  rw [hx, hy]
    -- Then we get 4*(6-1) = 4*5 = 20.
  norm_num