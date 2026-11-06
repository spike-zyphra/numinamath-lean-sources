import Mathlib

theorem inequalities_324543 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxp : x < 1) (hyq : y < 1) (hzr : z < 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - x) < 1 := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 1 - y := by linarith
  have h3 : 0 < 1 - z := by linarith
  nlinarith [mul_pos (sub_pos.mpr hxp) (sub_pos.mpr hyq), 
          mul_pos (sub_pos.mpr hxp) (sub_pos.mpr hzr), 
          mul_pos (sub_pos.mpr hyq) (sub_pos.mpr hzr),
          mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - y by linarith), 
          mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - z by linarith), 
          mul_nonneg (show 0 ≤ 1 - y by linarith) (show 0 ≤ 1 - z by linarith), 
          mul_nonneg hx hy, 
          mul_nonneg hy hz, 
          mul_nonneg hz hx 
        ]