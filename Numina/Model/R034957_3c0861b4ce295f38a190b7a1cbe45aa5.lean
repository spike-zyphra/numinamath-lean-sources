import Mathlib

theorem algebra_599692 (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) :
    |(a + b + c + a * b * c) / (1 + a * b + b * c + c * a)| < 1 := by
  have h1 : -1 < a := by linarith [abs_lt.mp ha]
  have h2 : a < 1 := by linarith [abs_lt.mp ha]
  have h3 : -1 < b := by linarith [abs_lt.mp hb]
  have h4 : b < 1 := by linarith [abs_lt.mp hb]
  have h5 : -1 < c := by linarith [abs_lt.mp hc]
  have h6 : c < 1 := by linarith [abs_lt.mp hc]
  have h7 : 0 < 1 + a * b + b * c + c * a := by
    nlinarith [mul_pos (sub_pos.mpr (show a + 1 > 0 by linarith)) (sub_pos.mpr (show b + 1 > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show a + 1 > 0 by linarith)) (sub_pos.mpr (show c + 1 > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show b + 1 > 0 by linarith)) (sub_pos.mpr (show c + 1 > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show 1 - a > 0 by linarith)) (sub_pos.mpr (show 1 - b > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show 1 - a > 0 by linarith)) (sub_pos.mpr (show 1 - c > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show 1 - b > 0 by linarith)) (sub_pos.mpr (show 1 - c > 0 by linarith))]
  have h8 : -1 < (a + b + c + a * b * c) / (1 + a * b + b * c + c * a) := by
    apply (lt_div_iff₀ (by nlinarith)).mpr
    nlinarith [mul_pos (sub_pos.mpr (show a + 1 > 0 by linarith)) (sub_pos.mpr (show b + 1 > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show a + 1 > 0 by linarith)) (sub_pos.mpr (show c + 1 > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show b + 1 > 0 by linarith)) (sub_pos.mpr (show c + 1 > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show 1 - a > 0 by linarith)) (sub_pos.mpr (show 1 - b > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show 1 - a > 0 by linarith)) (sub_pos.mpr (show 1 - c > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show 1 - b > 0 by linarith)) (sub_pos.mpr (show 1 - c > 0 by linarith))]
  have h10 : (a + b + c + a * b * c) / (1 + a * b + b * c + c * a) < 1 := by
    apply (div_lt_iff₀ (by nlinarith)).mpr
    nlinarith [mul_pos (sub_pos.mpr (show a + 1 > 0 by linarith)) (sub_pos.mpr (show b + 1 > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show a + 1 > 0 by linarith)) (sub_pos.mpr (show c + 1 > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show b + 1 > 0 by linarith)) (sub_pos.mpr (show c + 1 > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show 1 - a > 0 by linarith)) (sub_pos.mpr (show 1 - b > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show 1 - a > 0 by linarith)) (sub_pos.mpr (show 1 - c > 0 by linarith)), 
              mul_pos (sub_pos.mpr (show 1 - b > 0 by linarith)) (sub_pos.mpr (show 1 - c > 0 by linarith))]
  -- Use abs_lt to convert the goal to two inequalities
  rw [abs_lt]
  constructor
  · linarith
  · linarith