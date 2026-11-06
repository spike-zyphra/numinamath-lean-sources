import Mathlib

theorem algebra_3233 (x : ℝ) (hx : x ∈ Set.Icc (0) (Real.pi / 2)) (h : Real.cos x = 1 / 6) :
    Real.tan x = Real.sqrt 35 := by
  have hx1 : 0 ≤ x := hx.1
  have hx2 : x ≤ Real.pi / 2 := hx.2
  have h1 : Real.sin x ≥ 0 := by 
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hx1]
    · linarith [hx2, Real.pi_pos]
  have hsin2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h] at hsin2
  have hsin2' : Real.sin x ^ 2 = 35 / 36 := by
    nlinarith
  have hsin : Real.sin x = Real.sqrt 35 / 6 := by 
    have h4 : Real.sin x = Real.sqrt (35 / 36) := by
      have h5 : Real.sqrt (Real.sin x ^ 2) = Real.sin x := by
        rw [Real.sqrt_sq]
        linarith
      have h6 : Real.sqrt (Real.sin x ^ 2) = Real.sqrt (35 / 36) := by
        rw [hsin2']
      rw [h5] at h6
      linarith
    rw [h4]
    have : Real.sqrt (35 / 36) = Real.sqrt 35 / 6 := by
      calc
        Real.sqrt (35 / 36) = Real.sqrt ((35 : ℝ) / (6 ^ 2)) := by norm_num
        _ = Real.sqrt (35 : ℝ) / 6 := by 
          have h7 : Real.sqrt ((35 : ℝ) / (6 : ℝ) ^ 2) = Real.sqrt (35 : ℝ) / (6 : ℝ) := by 
            have h9 : Real.sqrt ((35 : ℝ) / (6 : ℝ) ^ 2) = Real.sqrt (35 : ℝ) / Real.sqrt ((6 : ℝ) ^ 2) := by 
              field_simp [Real.sqrt_div, Real.sqrt_sq]
            have h10 : Real.sqrt ((6 : ℝ) ^ 2) = (6 : ℝ) := by 
              rw [Real.sqrt_sq]
              all_goals linarith
            rw [h9, h10]
          rw [show (35 / 36 : ℝ) = (35 : ℝ) / (6 : ℝ) ^ 2 by ring] at *
          rw [h7]
          all_goals ring_nf <;> norm_num
    rw [this]
    all_goals norm_num
  rw [Real.tan_eq_sin_div_cos, hsin, h]
  field_simp
  <;> nlinarith