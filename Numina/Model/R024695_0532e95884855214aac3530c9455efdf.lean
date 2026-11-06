import Mathlib

theorem algebra_9528 (x : ℝ) (hx : Real.tan x = 3 / Real.sqrt 11) : 5 * Real.sin (2 * x) = 3 * Real.sqrt 11 / 2 := by
  have h1 : Real.cos x ≠ 0 := by
    by_contra h
    have htan : Real.tan x = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h]
    rw [htan] at hx
    field_simp at hx
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan] at hx
  have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  -- sin x = (3/√11)*cos x
  have h3 : Real.sin x = 3 / Real.sqrt 11 * Real.cos x := by
    have hcos : Real.cos x ≠ 0 := h1
    field_simp at hx ⊢
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
  
  have h4 : Real.cos x ^ 2 = 11 / 20 := by
    have h2' : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    rw [h3] at h2'
    -- (3/√11*cos x)^2 + cos^2 x = 1
    have h5 : (3 / Real.sqrt 11 * Real.cos x) ^ 2 + Real.cos x ^ 2 = 1 := by
      linarith
    -- (3/√11*cos x)^2 = (9/11)*cos^2 x
    have h6 : (3 / Real.sqrt 11 * Real.cos x) ^ 2 = (9 / 11) * Real.cos x ^ 2 := by
      calc
        (3 / Real.sqrt 11 * Real.cos x) ^ 2 = (9 / (Real.sqrt 11 * Real.sqrt 11)) * Real.cos x ^ 2 := by ring_nf
        _ = (9 / (11 : ℝ)) * Real.cos x ^ 2 := by
          have h11 : Real.sqrt 11 * Real.sqrt 11 = (11 : ℝ) := by
            calc
              Real.sqrt 11 * Real.sqrt 11 = (Real.sqrt 11) ^ 2 := by ring_nf
              _ = (11 : ℝ) := by
                rw [Real.sq_sqrt]
                all_goals linarith
          rw [h11]
          all_goals ring_nf
    rw [h6] at h5
    nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sqrt_nonneg 11]
  
  have h7 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    rw [Real.sin_two_mul]
  rw [h7]
  rw [h3]
  -- substitute; since usquation
  field_simp at *
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sqrt_nonneg 11, h4, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]