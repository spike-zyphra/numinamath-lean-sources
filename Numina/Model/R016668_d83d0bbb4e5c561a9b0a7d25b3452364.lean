import Mathlib

open Real

theorem algebra_283923 {f : ℝ → ℝ} (hf : f = fun x => 1 / (3 ^ x + sqrt 3)) :
    sqrt 3 * (f (-5) + f (-4) + f (-3) + f (-2) + f (-1) + f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6) = 6 := by
  have h1 : ∀ x, sqrt 3 * (f x + f (1 - x)) = 1 := by
    intro x
    rw [hf]
    have h3 : sqrt 3 * (1 / ((3 : ℝ) ^ x + sqrt 3) + 1 / ((3 : ℝ) ^ (1 - x : ℝ) + sqrt 3)) = 1 := by
      have h4 : (3 : ℝ) ^ (1 - x : ℝ) = (3 : ℝ) / (3 : ℝ) ^ x := by 
        rw [show (3 : ℝ) ^ (1 - x : ℝ) = (3 : ℝ) ^ (1 : ℝ) / (3 : ℝ) ^ (x : ℝ) by rw [← Real.rpow_sub]; ring_nf; all_goals norm_num]
        norm_num
      rw [h4]
      have h6 : (3 : ℝ) ^ x > 0 := by positivity
      field_simp [(show (3 : ℝ) ^ x ≠ 0 by positivity)]
      nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num : (0:ℝ) < 3), Real.sq_sqrt (show 0 ≤ (3: ℝ) by norm_num), sq_pos_of_pos (show (0 : ℝ) < sqrt 3 by positivity), sq_nonneg ((3 : ℝ) ^ x - 1 / sqrt 3), sq_nonneg ((3 : ℝ) ^ x - sqrt 3)]
    simpa using h3

  rw [hf]
  have h7 : sqrt 3 * (1 / ((3 : ℝ) ^ (-5 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (6 : ℝ) + sqrt 3)) = 1 := by
    have h24 : sqrt 3 * (f (-5 : ℝ) + f (1 - (-5 : ℝ) : ℝ)) = 1 := h1 (-5 : ℝ)
    have h25 : f (-5 : ℝ) = 1 / ((3 : ℝ) ^ (-5 : ℝ) + sqrt 3) := by 
      rw [hf]
    have h26 : f (1 - (-5 : ℝ) : ℝ) = 1 / ((3 : ℝ) ^ (1 - (-5 : ℝ) : ℝ) + sqrt 3) := by 
      rw [hf]
    rw [h25, h26] at h24
    have h9 : (1 - (-5 : ℝ) : ℝ) = (6 : ℝ) := by ring
    rw [h9] at h24
    linarith

  have h8 : sqrt 3 * (1 / ((3 : ℝ) ^ (-4 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (5 : ℝ) + sqrt 3)) = 1 := by
    have h24 : sqrt 3 * (f (-4 : ℝ) + f (1 - (-4 : ℝ) : ℝ)) = 1 := h1 (-4 : ℝ)
    have h25 : f (-4 : ℝ) = 1 / ((3 : ℝ) ^ (-4 : ℝ) + sqrt 3) := by 
      rw [hf]
    have h26 : f (1 - (-4 : ℝ) : ℝ) = 1 / ((3 : ℝ) ^ (1 - (-4 : ℝ) : ℝ) + sqrt 3) := by 
      rw [hf]
    rw [h25, h26] at h24
    have h9 : (1 - (-4 : ℝ) : ℝ) = (5 : ℝ) := by ring
    rw [h9] at h24
    linarith

  have h9 : sqrt 3 * (1 / ((3 : ℝ) ^ (-3 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (4 : ℝ) + sqrt 3)) = 1 := by
    have h24 : sqrt 3 * (f (-3 : ℝ) + f (1 - (-3 : ℝ) : ℝ)) = 1 := h1 (-3 : ℝ)
    have h25 : f (-3 : ℝ) = 1 / ((3 : ℝ) ^ (-3 : ℝ) + sqrt 3) := by 
      rw [hf]
    have h26 : f (1 - (-3 : ℝ) : ℝ) = 1 / ((3 : ℝ) ^ (1 - (-3 : ℝ) : ℝ) + sqrt 3) := by 
      rw [hf]
    rw [h25, h26] at h24
    have h9' : (1 - (-3 : ℝ) : ℝ) = (4 : ℝ) := by ring
    rw [h9'] at h24
    linarith

  have h10 : sqrt 3 * (1 / ((3 : ℝ) ^ (-2 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (3 : ℝ) + sqrt 3)) = 1 := by
    have h24 : sqrt 3 * (f (-2 : ℝ) + f (1 - (-2 : ℝ) : ℝ)) = 1 := h1 (-2 : ℝ)
    have h25 : f (-2 : ℝ) = 1 / ((3 : ℝ) ^ (-2 : ℝ) + sqrt 3) := by 
      rw [hf]
    have h26 : f (1 - (-2 : ℝ) : ℝ) = 1 / ((3 : ℝ) ^ (1 - (-2 : ℝ) : ℝ) + sqrt 3) := by 
      rw [hf]
    rw [h25, h26] at h24
    have h9 : (1 - (-2 : ℝ) : ℝ) = (3 : ℝ) := by ring
    rw [h9] at h24
    linarith

  have h11 : sqrt 3 * (1 / ((3 : ℝ) ^ (-1 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (2 : ℝ) + sqrt 3)) = 1 := by
    have h24 : sqrt 3 * (f (-1 : ℝ) + f (1 - (-1 : ℝ) : ℝ)) = 1 := h1 (-1 : ℝ)
    have h25 : f (-1 : ℝ) = 1 / ((3 : ℝ) ^ (-1 : ℝ) + sqrt 3) := by 
      rw [hf]
    have h26 : f (1 - (-1 : ℝ) : ℝ) = 1 / ((3 : ℝ) ^ (1 - (-1 : ℝ) : ℝ) + sqrt 3) := by 
      rw [hf]
    rw [h25, h26] at h24
    have h9 : (1 - (-1 : ℝ) : ℝ) = (2 : ℝ) := by ring
    rw [h9] at h24
    linarith

  have h12 : sqrt 3 * (1 / ((3 : ℝ) ^ (0 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (1 : ℝ) + sqrt 3)) = 1 := by
    have h24 : sqrt 3 * (f (0 : ℝ) + f (1 - (0 : ℝ) : ℝ)) = 1 := h1 (0 : ℝ)
    have h25 : f (0 : ℝ) = 1 / ((3 : ℝ) ^ (0 : ℝ) + sqrt 3) := by 
      rw [hf]
    have h26 : f (1 - (0 : ℝ) : ℝ) = 1 / ((3 : ℝ) ^ (1 - (0 : ℝ) : ℝ) + sqrt 3) := by 
      rw [hf]
    rw [h25, h26] at h24
    have h9 : (1 - (0 : ℝ) : ℝ) = (1 : ℝ) := by ring
    rw [h9] at h24
    linarith

  calc
    sqrt 3 * (1 / ((3 : ℝ) ^ (-5 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (-4 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (-3 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (-2 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (-1 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (0 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (1 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (2 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (3 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (4 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (5 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (6 : ℝ) + sqrt 3)) 
      = sqrt 3 * (1 / ((3 : ℝ) ^ (-5 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (6 : ℝ) + sqrt 3)) + 
        sqrt 3 * (1 / ((3 : ℝ) ^ (-4 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (5 : ℝ) + sqrt 3)) + 
        sqrt 3 * (1 / ((3 : ℝ) ^ (-3 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (4 : ℝ) + sqrt 3)) + 
        sqrt 3 * (1 / ((3 : ℝ) ^ (-2 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (3 : ℝ) + sqrt 3)) + 
        sqrt 3 * (1 / ((3 : ℝ) ^ (-1 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (2 : ℝ) + sqrt 3)) + 
        sqrt 3 * (1 / ((3 : ℝ) ^ (0 : ℝ) + sqrt 3) + 1 / ((3 : ℝ) ^ (1 : ℝ) + sqrt 3)) := by ring
    _ = 1 + 1 + 1 + 1 + 1 + 1 := by 
      rw [h7, h8, h9, h10, h11, h12]
    _ = 6 := by norm_num