import Mathlib

open Real

theorem algebra_6156 {x : ℝ} (hx : x > 0) (h : x = 15 / (2 + 15 / (2 + 15 / (2 + x)))) : x = 3 := by
  have h1 : 2 + x ≠ 0 := by
    linarith

  have h2 : 2 + x > 0 := by
    linarith

  field_simp [(show 2 + x ≠ 0 by linarith [h1]), 
    (show 2 + (15 / (2 + x)) ≠ 0 by 
      have h5 : (15 / (2 + x)) > 0 := by 
        apply div_pos
        norm_num
        linarith [show (2 + x) > 0 by linarith]
      nlinarith [show (2 + (15 / (2 + x))) > 0 by linarith]
    ), 
    (show 2 + (15 / (2 + (15 / (2 + x)))) ≠ 0 by 
      have h5 : (15 / (2 + x)) > 0 := by 
        apply div_pos
        norm_num
        linarith [show (2 + x) > 0 by linarith]
      have h6 : (2 + (15 / (2 + x))) > 0 := by nlinarith
      have h7 : (15 / (2 + (15 / (2 + x)))) > 0 := by 
        apply div_pos
        norm_num
        nlinarith
      nlinarith [show (2 + (15 / (2 + (15 / (2 + x))))) > 0 by linarith]
    )] at h
  
  have h_eq : (x - 3) * (x + 5) = 0 := by
    nlinarith
  
  cases' (mul_eq_zero.mp h_eq) with h_eq1 h_eq2
  · -- Case x - 3 = 0, so x = 3
    linarith
  
  · -- Case x + 5 = 0, so x = -5
    have h_eq2' : x = -5 := by linarith
    linarith [h_eq2', hx]