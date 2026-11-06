import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_190272 {x : ℝ} (hx : x > 0) :
    abs (3 - logb 2 x) < 2 ↔ x ∈ Ioo 2 32 := by
  constructor
  · -- Assume abs (3 - logb 2 x) < 2, prove x ∈ Ioo 2 32
    intro h
    have h1 : -2 < 3 - logb 2 x := by linarith [abs_lt.mp h]
    have h2 : 3 - logb 2 x < 2 := by linarith [abs_lt.mp h]
    have h3 : logb 2 x < 5 := by linarith
    have h32 : 1 < logb 2 x := by linarith
    have h4 : x < 32 := by 
      have h6 : logb 2 x < (5 : ℝ) := h3
      have h7 : logb 2 x < (5 : ℝ) := h6
      have h5_pos : (2 : ℝ) > (0 : ℝ) := by norm_num
      have h4_lt_5 : logb 2 x < (5 : ℝ) := h6

      have h5 : x < ((2 : ℝ) : ℝ) ^ (5 : ℝ) := by
        have h6' : logb 2 x < (5 : ℝ) := h4_lt_5
        have h7 : (logb 2 x : ℝ) < (5 : ℝ) := h4_lt_5
        have h8 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by
          rw [Real.rpow_logb]
          all_goals linarith
        have h8' : (2 : ℝ) ^ (logb 2 x : ℝ) < (2 : ℝ) ^ (5 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        linarith [h8, h8']
      have h5_rpow : (2 : ℝ) ^ (5 : ℝ) = (32 : ℝ) := by
        norm_num
      linarith [h5, h5_rpow]
    
    have h5 : 2 < x := by
      have h8 : (1 : ℝ) < (logb 2 x : ℝ) := h32
      have h1_lt : 1 < (logb 2 x : ℝ) := h8
      have h5_pos : (2 : ℝ) > (0 : ℝ) := by norm_num
      
      have h2rpow : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ (logb 2 x : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      have h6 : (2 : ℝ) ^ (logb 2 x : ℝ) = x := by
        rw [Real.rpow_logb]
        all_goals linarith
      have h7 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by
        norm_num
      have h8 : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ (logb 2 x : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      nlinarith [h2rpow, h6, h7, h6]
    
    constructor
    · -- 2 < x
      linarith
    · -- x < 32
      linarith
  
  · -- Assume x ∈ Ioo 2 32, prove abs (3 - logb 2 x) < 2
    rintro ⟨h1, h2⟩
    have h3 : 1 < (logb 2 x : ℝ) := by
      have h1' : 2 < x := by linarith
      have h2_pos : (2 : ℝ) > (0 : ℝ) := by norm_num
      have h3_pos : (x : ℝ) > (0 : ℝ) := by linarith
      have h4_lt : (2 : ℝ) ^ (1 : ℝ) < (x : ℝ) := by
        nlinarith
      have h5 : (2 : ℝ) ^ (1 : ℝ) < (x : ℝ) := h4_lt
      have h6 : (1 : ℝ) < (logb 2 x : ℝ) := by
        have h7 : (2 : ℝ) ^ (1 : ℝ) < (x : ℝ) := h5
        have h8 : (2 : ℝ) ^ (1 : ℝ) < (x : ℝ) := h7
        have h9_pos : (2 : ℝ) > (0 : ℝ) := by norm_num
        have h10_pos : (x : ℝ) > 0 := by linarith
        have h10 : (1 : ℝ) < (logb 2 x : ℝ) := by
          have h77 : (1 : ℝ) < (logb 2 x : ℝ) := by
            have h21 : logb 2 x = Real.logb (2 : ℝ) (x : ℝ) := by rfl
            rw [h21]
            have h22 : Real.logb (2 : ℝ) (x : ℝ) > (1 : ℝ) := by
              have h30 : Real.logb (2 : ℝ) (2 : ℝ) = (1 : ℝ) := by
                rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
              have h31 : Real.logb (2 : ℝ) (x : ℝ) > Real.logb (2 : ℝ) (2 : ℝ) := by
                apply Real.logb_lt_logb
                all_goals linarith
              linarith
            linarith
          nlinarith
        nlinarith
      nlinarith
  
    have h4 : (logb 2 x : ℝ) < (5 : ℝ) := by
      have h2' : x < (32 : ℝ) := by linarith
      have h2_pos : (2 : ℝ) > (0 : ℝ) := by norm_num
      have h5_pos : (x : ℝ) > (0 : ℝ) := by linarith
      -- show x < 32 implies logb 2 x < 5 by using exp properties
      have h6_lt : (x : ℝ) < (32 : ℝ) := by linarith
      have h7 : (x : ℝ) < (2 : ℝ) ^ (5 : ℝ) := by
        norm_num at h6_lt ⊢
        linarith

      have h8 : (logb 2 x : ℝ) < (5 : ℝ) := by
        have h9 : (x : ℝ) < (2 : ℝ) ^ (5 : ℝ) := h7
        have h10_pos : (2 : ℝ) > (0 : ℝ) := by norm_num
        have h11_pos : (x : ℝ) > (0 : ℝ) := by linarith
        have h12 : (logb 2 x : ℝ) < (5 : ℝ) := by
          have h7' : (x : ℝ) < (2 : ℝ) ^ (5 : ℝ) := h9
          have h8 : (logb 2 x : ℝ) = Real.logb (2 : ℝ) (x : ℝ) := by rfl
          rw [h8]
          have h9' : Real.logb (2 : ℝ) (x : ℝ) < (5 : ℝ) := by
            have h100 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (5 : ℝ)) = (5 : ℝ) := by
              rw [Real.logb_rpow]
              all_goals linarith
            have h101 : (x : ℝ) < ((2 : ℝ) ^ (5 : ℝ) : ℝ) := by linarith
            have h102_pos : (2 : ℝ) > (0 : ℝ) := by norm_num
            have h103_pos : (x : ℝ) > 0 := by linarith
            have h104_pos : ((2 : ℝ) ^ (5 : ℝ) : ℝ) > 0 := by positivity
            have h105 : Real.logb (2 : ℝ) (x : ℝ) < Real.logb (2 : ℝ) ((2 : ℝ) ^ (5 : ℝ)) := by
              apply Real.logb_lt_logb
              all_goals linarith
            linarith [h100, h105, h100, h105]
          linarith
        linarith
      linarith
  
    have h1 : -2 < (3 - (logb 2 x : ℝ)) := by linarith
    have h2 : (3 - (logb 2 x : ℝ)) < (2 : ℝ) := by linarith 
    apply abs_lt.mpr
    constructor <;> linarith
  all_goals try linarith