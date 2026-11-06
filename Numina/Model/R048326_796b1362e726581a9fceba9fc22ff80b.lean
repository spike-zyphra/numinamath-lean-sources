import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_104092
  (a b c : ℝ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (h : a + b > c)
  (h' : a + c > b)
  (h'' : b + c > a) :
  a^2 * c * (a - b) + b^2 * a * (b - c) + c^2 * b * (c - a) ≥ 0 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - c + b),
            sq_nonneg (b - c + a), sq_nonneg (b - a + c),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
            mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
          ]