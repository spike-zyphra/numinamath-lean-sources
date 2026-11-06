import Mathlib

open Real

theorem algebra_290347 {f g : ℝ → ℝ} (hf : f = fun x => 9 ^ x)
    (hg : g = fun x => logb 3 (9 * x)) (x : ℝ) (hx : g (f x) = f (g 2)) :
    x = 161 := by
  have h1 : g (f x) = 2 + 2 * x := by 
    rw [hf, hg]
    simp
    have h3 : (9 * ((9 : ℝ) ^x) ) = (3 : ℝ) ^ (2 + 2 * x : ℝ) := by
      calc
        9 * ((9 : ℝ) ^x ) = (9 : ℝ) ^ (1 + x : ℝ) := by 
          rw [show (9 : ℝ) ^ (1 + x : ℝ) = 9 * (9 : ℝ) ^x by 
            rw [Real.rpow_add]
            ring_nf
            all_goals norm_num
          ]
        _ = ((3 ^ (2 : ℝ) ) ) ^ (1 + x : ℝ) := by 
          norm_num
        _ = (3 : ℝ) ^ (2 * (1 + x) : ℝ) := by 
          rw [← Real.rpow_mul]
          ring
          all_goals norm_num
        _ = (3 : ℝ) ^ (2 + 2 * x : ℝ) := by 
          ring_nf
    rw [h3]
    have h4 : logb (3 : ℝ) ((3 : ℝ) ^ (2 + 2 * x : ℝ)) = (2 + 2 * x : ℝ) := by
      exact logb_rpow (by norm_num) (by norm_num)
    have h5 : (3 : ℝ) > 1 := by norm_num
    have h6 : (3 : ℝ) ^ (2 + 2 * x : ℝ) > 0 := by positivity
    have h44 : logb (3 : ℝ) ((3 : ℝ) ^ (2 + 2 * x : ℝ)) = (2 + 2 * x : ℝ) := by
      exact logb_rpow (by norm_num) (by norm_num)
    linarith
  have h2 : f (g 2) = 324 := by
    rw [hf, hg]
    simp
    have h3 : logb 3 (9 * (2 : ℝ) ) = 2 + logb 3 (2 : ℝ) := by 
      have h4 : (9 * (2 : ℝ) ) = (9 : ℝ) * (2 : ℝ) := by ring
      rw [h4]
      have h5 : logb 3 (9 * 2) = logb 3 (9 : ℝ) + logb 3 (2 : ℝ) := by 
        rw [logb_mul (by norm_num) (by norm_num)]
      rw [h5]
      have h6 : logb 3 (9 : ℝ) = (2 : ℝ) := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      rw [h6]
    have h4 : (9 : ℝ) ^ (logb 3 (9 * (2 : ℝ)) : ℝ) = 324 := by 
      rw [h3]
      have h5 : (9 : ℝ) ^ (2 + logb 3 (2 : ℝ) ) = (3 : ℝ) ^ (2 * (2 + logb 3 (2 : ℝ)) ) := by
        have h6 : (9 : ℝ) ^ (2 + logb 3 (2 : ℝ)) = ((3 : ℝ) ^ (2 : ℝ) ) ^ (2 + logb 3 (2 : ℝ) ) := by 
          norm_num
        rw [h6]
        have h7 : ((3 : ℝ) ^ (2 : ℝ) ) ^ (2 + logb 3 (2 : ℝ)) = (3 : ℝ) ^ (2 * (2 + logb 3 (2 : ℝ) ) ) := by 
          rw [← Real.rpow_mul]
          ring
          all_goals norm_num
        rw [h7]
      rw [h5]
      have h9 : (3 : ℝ) ^ (2 * (2 + logb 3 (2 : ℝ)) ) = 324 := by 
        have h44 : (3 : ℝ) ^ (2 * (2 + logb 3 (2 : ℝ)) ) 
          = (3 : ℝ) ^ (4 + 2 * logb 3 (2 : ℝ) ) := by ring
        rw [h44]
        have h6 : (3 : ℝ) ^ (4 + 2 * logb 3 (2 : ℝ) ) 
          = (3 : ℝ) ^ (4 : ℝ) * (3 : ℝ) ^ (2 * logb 3 (2 : ℝ)) := by 
          rw [← Real.rpow_add]
          ring
          all_goals norm_num
        rw [h6]
        have h7 : (3 : ℝ) ^ (2 * logb 3 (2 : ℝ)) 
          = ((3 : ℝ) ^ (logb 3 (2 : ℝ) ) ) ^ (2 : ℝ) := by 
          rw [← Real.rpow_mul]
          ring
          all_goals norm_num
        have h8 : (3 : ℝ) ^ (logb 3 (2 : ℝ) ) = (2 : ℝ) := by 
          rw [Real.rpow_logb]
          all_goals norm_num
        have h55 : ((3 : ℝ) ^ (logb 3 (2 : ℝ) ) ) ^ (2 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
          rw [h8]
        have h555 : (3 : ℝ) ^ (4 : ℝ) 
          = (81 : ℝ) := by
          norm_num
        rw [h7, h55, h555]
        norm_num
      linarith
    linarith
  rw [h1, h2] at hx
  linarith