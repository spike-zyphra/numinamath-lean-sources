import Mathlib

theorem algebra_607143 (a b c : ℝ) (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2) (hc : 0 ≤ c ∧ c ≤ 2) : (a - b) * (b - c) * (a - c) ≤ 2 := by 
  have ha1 : 0 ≤ a := ha.1
  have ha2 : a ≤ 2 := ha.2
  have hb1 : 0 ≤ b := hb.1
  have hb2 : b ≤ 2 := hb.2
  have hc1 : 0 ≤ c := hc.1
  have hc2 : c ≤ 2 := hc.2
  nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 2 - a by linarith), 
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 2 - b by linarith), 
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ 2 - c by linarith), 
          mul_nonneg (sub_nonneg.mpr (show a ≤ 2 by linarith)) (sub_nonneg.mpr (show b ≥ 0 by linarith)), 
          mul_nonneg (sub_nonneg.mpr (show b ≤ 2 by linarith)) (sub_nonneg.mpr (show c ≥ 0 by linarith)), 
          mul_nonneg (sub_nonneg.mpr (show a ≤ 2 by linarith)) (sub_nonneg.mpr (show c ≥ 0 by linarith)), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ 2 - a by linarith) (show (0 : ℝ) ≤ 2 - b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ 2 - a by linarith) (show (0 : ℝ) ≤ 2 - c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ 2 - b by linarith) (show (0 : ℝ) ≤ 2 - c by linarith)
  ]