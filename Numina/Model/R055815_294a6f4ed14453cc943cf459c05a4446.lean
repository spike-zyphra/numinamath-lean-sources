import Mathlib

theorem inequalities_176887 (x y : ℝ) (hx : x ∈ Set.Ioo 0 1) (hy : y ∈ Set.Ioo 0 1) :
    x^3 + x * y^2 + 2 * x * y ≤ 2 * x^2 * y + x^2 + x + y := by
  rw [Set.mem_Ioo] at hx hy
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - y / 2), sq_nonneg (y - 1/2), sq_nonneg (x - 1/2), 
          sq_nonneg (x * y - 1/4), mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr hy.2), 
          mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr hx.1), mul_pos (sub_pos.mpr hy.2) (sub_pos.mpr hy.1), 
          sq_nonneg (x * (x - y)), sq_nonneg (y * (x - y)), 
          hx.1, hx.2, hy.1, hy.2]