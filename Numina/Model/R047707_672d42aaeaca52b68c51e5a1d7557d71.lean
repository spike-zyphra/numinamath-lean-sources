import Mathlib

theorem algebra_197661 {f : ℝ → ℝ} (hf : f = fun x => (x ^ 4 + 2 * x ^ 3 + 4 * x - 5) ^ 2004 + 2004)
    (d : ℝ) (hd : d = f (Real.sqrt 3 - 1)) : d = 2005 := by

  rw [hd, hf]
  have h1 : (Real.sqrt 3 - 1 : ℝ) ^ 2 = 4 - 2 * Real.sqrt 3 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    
  have h2 : (Real.sqrt 3 - 1 : ℝ) ^ 3 = 6 * Real.sqrt 3 - 10 := by
    calc
      (Real.sqrt 3 - 1 : ℝ) ^ 3 = (Real.sqrt 3 - 1 : ℝ) * ((Real.sqrt 3 - 1 : ℝ) ^ 2) := by ring
      _ = (Real.sqrt 3 - 1 : ℝ) * (4 - 2 * Real.sqrt 3) := by rw [h1]
      _ = 6 * Real.sqrt 3 - 10 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
  have h3 : (Real.sqrt 3 - 1 : ℝ) ^ 4 = 28 - 16 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3 - 1 : ℝ) ^ 4 = (Real.sqrt 3 - 1 : ℝ) * ((Real.sqrt 3 - 1 : ℝ) ^ 3) := by ring
      _ = (Real.sqrt 3 - 1 : ℝ) * (6 * Real.sqrt 3 - 10) := by rw [h2]
      _ = 28 - 16 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
  have h4 : ((Real.sqrt 3 - 1 : ℝ) ^ 4 + 2 * (Real.sqrt 3 - 1 : ℝ) ^ 3 + 4 * (Real.sqrt 3 - 1 : ℝ) - 5) = -1 := by
    nlinarith [h1, h2, h3, Real.sqrt_pos.mpr (show 0 < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
  norm_num [h4]
  <;> nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ 3)]