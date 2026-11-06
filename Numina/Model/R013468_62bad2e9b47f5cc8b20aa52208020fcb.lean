import Mathlib

open Real
open scoped BigOperators

theorem inequalities_42878 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
  (hxy : (x - 1) * (y - 1) ≥ 1) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a^2 * x + b^2 * y > c^2 := by 
  have h3 : x * y ≥ x + y := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), 
      mul_pos hx hy, 
      hxy 
      ]
  have h4 : a^2 * x + b^2 * y - (a + b)^2 ≥ 0 := by 
    nlinarith [sq_nonneg (a * x - b * y), sq_nonneg (a - b), sq_nonneg (a * (x - 1) - b * (y - 1)), sq_nonneg (a * (y - 1) - b * (x - 1)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos hx hy, 
      hxy 
      ]
  have h5 : (a + b)^2 ≤ a^2 * x + b^2 * y := by 
    linarith [h4]

  have h6 : (a + b) ^ 2 > c ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a * (x - 1) - b * (y - 1)), 
    sq_nonneg (a * (y - 1) - b * (x - 1)), sq_nonneg (a * x - b * y), 
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
    mul_pos hx hy, 
    h6, h5, sq_nonneg (a + b - c)
    ]