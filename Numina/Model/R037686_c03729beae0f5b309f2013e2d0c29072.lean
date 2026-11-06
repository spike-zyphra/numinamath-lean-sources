import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_123297 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a / (b + c) + b / (c + a) + c / (a + b) < 2 :=
by

  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith

  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 2 < 0 := by

    have h5 : 0 < (b + c) * (c + a) * (a + b) := by
      positivity

    have h6 : a / (b + c) + b / (c + a) + c / (a + b) - 2 = (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring

    rw [h6]

    have h7 : a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b) < 0 := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
        mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
      ]

    apply div_neg_of_neg_of_pos 
    linarith 
    all_goals 
      positivity
  
  linarith