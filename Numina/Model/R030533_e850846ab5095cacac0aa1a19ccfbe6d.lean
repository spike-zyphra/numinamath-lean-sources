import Mathlib

theorem algebra_18928 {x : ℝ} (hx : x ≥ 0) :
    (x * (x * (x * x^ (1 / 2 : ℝ))^ (1 / 3 : ℝ))^ (1 / 3 : ℝ)) ^ (1 / 3 : ℝ) = x ^ (1 / 2 : ℝ) := by
  have h21 : x * x ^ (1 / 2 : ℝ) = x ^ (3 / 2 : ℝ) := by
    by_cases h : x = 0
    · -- x = 0
      rw [h]
      norm_num
    · -- x > 0
      have hx_pos : x > 0 := by
        by_contra h'
        push_neg at h'
        have : x = 0 := by linarith
        contradiction
      have h3 : x ^ (3 / 2 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by ring]
        rw [Real.rpow_add]
        norm_num
        all_goals nlinarith
      rw [h3]
      simp at *
  have h22 : (x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) = x ^ (1 / 2 : ℝ) := by
    by_cases h : x = 0
    · -- x = 0
      rw [h]
      norm_num
    · -- x > 0
      have hx_pos : x > 0 := by
        by_contra h'
        push_neg at h'
        have : x = 0 := by linarith
        contradiction
      have h4 : (x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) = x ^ ((3 / 2 : ℝ) * (1 / 3 : ℝ)) := by 
        rw [← Real.rpow_mul]
        ring_nf
        all_goals nlinarith
      rw [h4]
      norm_num
  have h23 : x * ((x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)) = x ^ (3 / 2 : ℝ) := by 
    rw [h22]
    have h24 : x * x ^ (1 / 2 : ℝ) = x ^ (3 / 2 : ℝ) := h21
    linarith [h24]
  have h24 : (x * ((x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)) ) ^ (1 / 3 : ℝ) = x ^ (1 / 2 : ℝ) := by 
    rw [h23]
    exact_mod_cast h22
  have h25 : x * ((x * ((x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)) ) ^ (1 / 3 : ℝ)) = x ^ (3 / 2 : ℝ) := by
    rw [h24]
    have h26 : x * x ^ (1 / 2 : ℝ) = x ^ (3 / 2 : ℝ) := h21
    linarith [h26]
  have h26 : (x * ((x * ((x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)) ) ^ (1 / 3 : ℝ)) ) ^ (1 / 3 : ℝ) = x ^ (1 / 2 : ℝ) := by 
    rw [h25]
    exact_mod_cast h22
  have h27 : x * (x * (x * x^ (1 / 2 : ℝ))^ (1 / 3 : ℝ))^ (1 / 3 : ℝ) = x * ((x * ((x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)) ) ^ (1 / 3 : ℝ) ) := by 
    have h33 : (x * (x * x ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ)) ^ (1 / 3 : ℝ) = (x * ((x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)) ) ^ (1 / 3 : ℝ) := by 
      have h34 : x * (x * x ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) = x * ((x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)) := by
        have h35 : x * x ^ (1 / 2 : ℝ) = x ^ (3 / 2 : ℝ) := h21 
        have h36 : (x * x ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) = (x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) := by 
          rw [show x * x ^ (1 / 2 : ℝ) = x ^ (3 / 2 : ℝ) by linarith [h35]]
        rw [h36]
      rw [h34]
    rw [h33]
  rw [h27]
  exact_mod_cast h26