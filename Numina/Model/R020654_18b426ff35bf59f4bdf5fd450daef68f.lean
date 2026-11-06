import Mathlib

theorem inequalities_599790 (x y z w : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w) :
    2/3 ≤ x/(y + 2*z + 3*w) + y/(z + 2*w + 3*x) + z/(w + 2*x + 3*y) + w/(x + 2*y + 3*z) := by 
  have h1 : 0 < y + 2 * z + 3 * w := by positivity
  have h2 : 0 < z + 2 * w + 3 * x := by positivity
  have h3 : 0 < w + 2 * x + 3 * y := by positivity
  have h4 : 0 < x + 2 * y + 3 * z := by positivity
  have h5 : x/(y + 2*z + 3*w) + y/(z + 2*w + 3*x) + z/(w + 2*x + 3*y) + w/(x + 2*y + 3*z) - 2/3 ≥ 0 := by
    have h6 : 0 < (y + 2 * z + 3 * w) * (z + 2 * w + 3 * x) * (w + 2 * x + 3 * y) * (x + 2 * y + 3 * z) := by positivity
    have h7 : x/(y + 2*z + 3*w) + y/(z + 2*w + 3*x) + z/(w + 2*x + 3*y) + w/(x + 2*y + 3*z) - 2/3 =
        (x*(z + 2*w + 3*x)*(w + 2*x + 3*y)*(x + 2*y + 3*z) +
         y*(y + 2*z + 3*w)*(w + 2*x + 3*y)*(x + 2*y + 3*z) +
         z*(y + 2*z + 3*w)*(z + 2*w + 3*x)*(x + 2*y + 3*z) +
         w*(y + 2*z + 3*w)*(z + 2*w + 3*x)*(w + 2*x + 3*y) -
         2/3*(y + 2*z + 3*w)*(z + 2*w + 3*x)*(w + 2*x + 3*y)*(x + 2*y + 3*z)) /
        ((y + 2*z + 3*w)*(z + 2*w + 3*x)*(w + 2*x + 3*y)*(x + 2*y + 3*z)) := by
      field_simp
      ring
    rw [h7]
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w), sq_nonneg (y - z), sq_nonneg (y - w), sq_nonneg (z - w),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (x * (x - w)),
        sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - w)),
        sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), sq_nonneg (z * (z - w)),
        sq_nonneg (w * (w - x)), sq_nonneg (w * (w - y)), sq_nonneg (w * (w - z)),
        mul_pos hx hy, mul_pos hx hz, mul_pos hx hw, 
        mul_pos hy hz, mul_pos hy hw, 
        mul_pos hz hw
        ]
    all_goals positivity
  linarith