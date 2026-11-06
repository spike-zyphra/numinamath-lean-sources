import Mathlib

theorem inequalities_264739 (x y z : ℝ) (h₀ : 0 < x) (h₁ : x < y) (h₂ : y < z) (h₃ : z < 1) :
    x ^ 2 + y ^ 2 + z ^ 2 < x * y + y * z + z * x + z - x := by
  have h4 : 0 < y := by linarith
  have h5 : 0 < z := by linarith
  have h6 : y - x > 0 := by nlinarith
  have h7 : z - y > 0 := by nlinarith
  have h8 : 1 - z > 0 := by linarith
  have h9 : z - x > 0 := by nlinarith

  nlinarith [mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), 
          mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃), 
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          mul_pos (show (0 : ℝ) < z - x by nlinarith) (show (0 : ℝ) < z - y by nlinarith), 
          mul_pos (show (0 : ℝ) < z - y by nlinarith) (show (0 : ℝ) < y - x by nlinarith), 
          mul_pos (show (0 : ℝ) < y - x by nlinarith) (show (0 : ℝ) < z - x by nlinarith), 
          mul_pos (show (0 : ℝ) < z by linarith) (show (0 : ℝ) < 1 - z by nlinarith)]