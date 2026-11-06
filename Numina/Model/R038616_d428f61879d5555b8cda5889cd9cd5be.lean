import Mathlib

open Real

theorem algebra_218668 {f : ℝ → ℝ} (hf : f = fun x => 2^x - 2^(1 - x)) :
    sqrt ((f 2015) - (f 2014) + (f 1) - (f 0)) = 2^1007 + 2^(-1007 : ℤ) := by
  have h1 : (f 2015 : ℝ) = (2 : ℝ) ^ (2015 : ℝ) - (2 : ℝ) ^ (-2014 : ℝ) := by
    rw [hf]
    norm_num
  have h2 : (f 2014 : ℝ) = (2 : ℝ) ^ (2014 : ℝ) - (2 : ℝ) ^ (-2013 : ℝ) := by
    rw [hf]
    norm_num
  have h3 : (f 1 : ℝ) = 1 := by
    rw [hf]
    norm_num
  have h4 : (f 0 : ℝ) = -1 := by
    rw [hf]
    norm_num
  have h5 : (f 2015 : ℝ) - (f 2014 : ℝ) + (f 1 : ℝ) - (f 0 : ℝ) = (2 : ℝ) ^ (2014 : ℝ) + (2 : ℝ) ^ (-2014 : ℝ) + 2 := by 
    rw [h1, h2, h3, h4]
    ring_nf
  have h6 : (f 2015 : ℝ) - (f 2014 : ℝ) + (f 1 : ℝ) - (f 0 : ℝ) = ((2^1007 + (2 : ℝ) ^ (-1007 : ℤ)) ) ^ 2 := by
    rw [h5]
    have h7 : ( (2 : ℝ) ^ (2014 : ℝ) ) = ( (2 : ℝ) ^ (1007 : ℝ) ) ^ 2 := by
      have h8 : ( (2 : ℝ) ^ (2014 : ℝ) ) = ( (2 : ℝ) ^ (1007 : ℝ) ) ^ 2 := by
        calc
          ( (2 : ℝ) ^ (2014 : ℝ) ) = (2 : ℝ) ^ (2 * (1007 : ℝ)) := by norm_num
          _ = ( ( (2 : ℝ) ^ (1007 : ℝ) ) ^ 2 ) := by 
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul]
            ring_nf
            all_goals norm_num
      linarith
    have h8 : ( (2 : ℝ) ^ (-2014 : ℝ) ) = ( (2 : ℝ) ^ (-1007 : ℤ) ) ^ 2 := by
      rw [show (-2014 : ℝ) = (2 : ℕ) * (-1007 : ℤ) by norm_num]
      rw [← zpow_natCast, ← zpow_mul]
      all_goals norm_num
    have h9 : ( (2 : ℝ) ^ (1007 : ℝ) ) = ( (2 : ℝ) ^ (1007 : ℤ) ) := by 
      norm_num
    rw [h7, h8, h9]
    all_goals 
      ring_nf
    all_goals norm_num
  rw [h6]
  have h_nonneg : (0 : ℝ) ≤ (2^1007 + (2 : ℝ) ^ (-1007 : ℤ)) := by
    have h1_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (1007 : ℤ) := by positivity
    have h2_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-1007 : ℤ) := by positivity
    linarith
  rw [Real.sqrt_sq (h_nonneg)]
  all_goals norm_num