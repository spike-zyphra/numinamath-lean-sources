import Mathlib

theorem inequalities_313804 (x y z : ℝ) (hx : x ∈ Set.Ioo 0 1) (hy : y ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - x) < 1 := by 
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  rcases hz with ⟨hz0, hz1⟩
  nlinarith [mul_pos hx0 hy0, mul_pos hx0 hz0, mul_pos hy0 hz0, 
          mul_pos (sub_pos.mpr hx0) (sub_pos.mpr hy0), 
          mul_pos (sub_pos.mpr hx0) (sub_pos.mpr hz0), 
          mul_pos (sub_pos.mpr hy0) (sub_pos.mpr hz0), 
          mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1), 
          mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hz1), 
          mul_pos (sub_pos.mpr hy1) (sub_pos.mpr hz1), 
          mul_pos (sub_pos.mpr hx0) (sub_pos.mpr hy0), 
          mul_pos (sub_pos.mpr hx0) (sub_pos.mpr hz0), 
          mul_pos (sub_pos.mpr hy0) (sub_pos.mpr hz0)]