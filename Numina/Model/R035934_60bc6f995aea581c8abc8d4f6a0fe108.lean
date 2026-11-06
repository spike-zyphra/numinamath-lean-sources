import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_127403 (a b c : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a / (b + c) + b / (a + c) + c / (b + a) < 5 / 2 := by
  have pos1 : 0 < b + c := by linarith
  have pos2 : 0 < a + c := by linarith
  have pos3 : 0 < b + a := by linarith
  have h1 : a / (b + c) + b / (a + c) + c / (b + a) - 5 / 2 < 0 := by
    have pos1 : 0 < b + c := by linarith
    have pos2 : 0 < a + c := by linarith
    have pos3 : 0 < b + a := by linarith
    have h1 : 0 < (b + c) * (a + c) * (b + a) := by
      positivity
    have h2 : a / (b + c) + b / (a + c) + c / (b + a) - 5 / 2 = (a * (a + c) * (b + a) + b * (b + c) * (b + a) + c * (b + c) * (a + c) - (5 / 2) * (b + c) * (a + c) * (b + a)) / ((b + c) * (a + c) * (b + a)) := by
      field_simp
      ring
    rw [h2] at *
    apply div_neg_of_neg_of_pos
    · -- Show Numerator < 0
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), -- `a + b > c`, `a + c > b`
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), -- `a + b > c`, `b + c > a`
        mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')] -- `a + c > b`, `b + c > a`
    · -- Show Denominator > 0
      positivity
  linarith