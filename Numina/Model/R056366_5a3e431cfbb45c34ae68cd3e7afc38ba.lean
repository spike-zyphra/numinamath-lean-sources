import Mathlib

theorem inequalities_597837
    (x y z : ℝ)
    (hx : x ∈ Set.Ioo 0 1)
    (hy : y ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) :
    x * (1 - y) * (1 - z) + y * (1 - z) * (1 - x) + z * (1 - x) * (1 - y) < 1 := by 
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  rcases hz with ⟨hz0, hz1⟩
  -- We need to prove x * (1 - y) * (1 - z) + y * (1 - z) * (1 - x) + z * (1 - x) * (1 - y) < 1
  -- Expanding and simplifying will show it's a cubic expression in variables less than 1.
  nlinarith [mul_pos hx0 hy0, mul_pos hx0 hz0, mul_pos hy0 hz0,
          mul_pos (sub_pos.mpr hx0) (sub_pos.mpr hx1),
          mul_pos (sub_pos.mpr hy0) (sub_pos.mpr hy1),
          mul_pos (sub_pos.mpr hz0) (sub_pos.mpr hz1),
          mul_pos (show (0 : ℝ) < 1 - y by linarith) (show (0 : ℝ) < 1 - z by linarith),
          mul_pos (show (0 : ℝ) < 1 - x by linarith) (show (0 : ℝ) < 1 - y by linarith),
          mul_pos (show (0 : ℝ) < 1 - x by linarith) (show (0 : ℝ) < 1 - z by linarith),
          mul_pos (show (0 : ℝ) < y by linarith) (show (0 : ℝ) < z by linarith),
          mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < z by linarith),
          mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < y by linarith)]