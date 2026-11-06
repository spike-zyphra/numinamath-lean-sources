import Mathlib

theorem inequalities_142825
    (a b c : ℝ)
    (ha : |a| < 1)
    (hb : |b| < 1)
    (hc : |c| < 1) :
    a * b + b * c + c * a + 1 > 0 := by
  have h1 : -1 < a := by linarith [abs_lt.mp ha]
  have h2 : a < 1 := by linarith [abs_lt.mp ha]
  have h3 : -1 < b := by linarith [abs_lt.mp hb]
  have h4 : b < 1 := by linarith [abs_lt.mp hb]
  have h5 : -1 < c := by linarith [abs_lt.mp hc]
  have h6 : c < 1 := by linarith [abs_lt.mp hc]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b + c - 1), sq_nonneg (a + b + c + 1),
    mul_pos (sub_pos.mpr (show -1 < a from by linarith)) (sub_pos.mpr (show a < 1 from by linarith)), 
    mul_pos (sub_pos.mpr (show -1 < b from by linarith)) (sub_pos.mpr (show b < 1 from by linarith)), 
    mul_pos (sub_pos.mpr (show -1 < c from by linarith)) (sub_pos.mpr (show c < 1 from by linarith)), 
    mul_pos (sub_pos.mpr (show -1 < a from by linarith)) (sub_pos.mpr (show -1 < b from by linarith)), 
    mul_pos (sub_pos.mpr (show -1 < a from by linarith)) (sub_pos.mpr (show -1 < c from by linarith)), 
    mul_pos (sub_pos.mpr (show -1 < b from by linarith)) (sub_pos.mpr (show -1 < c from by linarith)), 
    mul_pos (sub_pos.mpr (show a < 1 from by linarith)) (sub_pos.mpr (show b < 1 from by linarith)), 
    mul_pos (sub_pos.mpr (show a < 1 from by linarith)) (sub_pos.mpr (show c < 1 from by linarith)), 
    mul_pos (sub_pos.mpr (show b < 1 from by linarith)) (sub_pos.mpr (show c < 1 from by linarith))
  ]