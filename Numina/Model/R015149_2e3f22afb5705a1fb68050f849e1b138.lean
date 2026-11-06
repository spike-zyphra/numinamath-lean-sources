import Mathlib

theorem inequalities_312193
    (x y z : ℝ)
    (hx : 0 < x ∧ x < 1)
    (hy : 0 < y ∧ y < 1)
    (hz : 0 < z ∧ z < 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - x) < 1 := by
  have hx1 : 0 < x := hx.1
  have hx2 : x < 1 := hx.2
  have hy1 : 0 < y := hy.1
  have hy2 : y < 1 := hy.2
  have hz1 : 0 < z := hz.1
  have hz2 : z < 1 := hz.2
  nlinarith [mul_pos hx1 hy1, mul_pos hx1 hz1, mul_pos hy1 hz1,
          mul_pos (sub_pos.mpr hx2) (sub_pos.mpr hy2), 
          mul_pos (sub_pos.mpr hx2) (sub_pos.mpr hz2), 
          mul_pos (sub_pos.mpr hy2) (sub_pos.mpr hz2),
          mul_pos hx1 (sub_pos.mpr hx2), 
          mul_pos hy1 (sub_pos.mpr hy2), 
          mul_pos hz1 (sub_pos.mpr hz2)
]