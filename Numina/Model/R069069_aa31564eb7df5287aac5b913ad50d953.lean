import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_249015 (a b c : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a * (b - c)^2 + b * (c - a)^2 + c * (a - b)^2 + 4 * a * b * c > a^3 + b^3 + c^3 := by
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)
          ]