import Mathlib
/-While walking on a plane surface, a traveler first headed 19 miles north, then 16 miles west, then 3 miles south and finally 4 miles east. How many miles from the starting point was the traveler after these four legs of the journey?-/
theorem algebra_21536 {O A move_north move_west move_south move_east : EuclideanSpace ℝ (Fin 2)} (a b : ℝ) (h : O = ![a, b])
    (hn: move_north = ![0,19]) (hw: move_west = ![-16,0])(hs: move_south = ![0,-3])(he: move_east = ![4,0])
    (hA : A =  O + move_north + move_west + move_south + move_east)  : dist O A = 20:= by
    --In total, the traveler went 16 miles north and 12 miles west.
    rw [hn,hw,hs,he,h] at hA; rw [h,hA]
    rw [dist_eq_norm]
    --This forms a 12-16-20 (3-4-5) Pythagorean triple, so the traveler is $\boxed{20}$ miles away from the starting point.
    rw [norm_eq_sqrt_real_inner]
    norm_num;ring_nf
    --proof √400 = 20
    have sqrt400 : √400 = 20 := by
      rw[show (400 : ℝ) = 20 ^ 2 by ring_nf]
      rw[Real.sqrt_sq_eq_abs]
      norm_num
    rw [sqrt400]