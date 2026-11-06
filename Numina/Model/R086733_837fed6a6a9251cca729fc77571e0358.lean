import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_133597 (a b c : ℝ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (h : a + b > c)
  (h' : a + c > b)
  (h'' : b + c > a) :
  a^3 + b^3 + 3 * a * b * c > c^3 := by
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), -- (a + b - c) > 0 and (a + c - b) > 0
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), -- (a + b - c) > 0 and (b + c - a) > 0
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h'') -- (a + c - b) > 0 and (b + c - a) > 0
]