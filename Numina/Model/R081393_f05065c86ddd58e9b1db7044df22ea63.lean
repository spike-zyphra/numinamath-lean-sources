import Mathlib

theorem calculus_23137 (a b : ℝ) (ha : Real.cos a = 1 / 3) (hb : Real.cos b = 1 / 4) :
    Real.cos (a + b) * Real.cos (a - b) = -119 / 144 := by
  have h1 : Real.sin a ^ 2 = 8 / 9 := by
    have hsin : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
    rw [ha] at hsin
    have : Real.sin a ^ 2 = 1 - (1 / 3) ^ 2 := by linarith
    rw [this]
    norm_num
  have h2 : Real.sin b ^ 2 = 15 / 16 := by
    have hsin : Real.sin b ^ 2 + Real.cos b ^ 2 = 1 := Real.sin_sq_add_cos_sq b
    rw [hb] at hsin
    have : Real.sin b ^ 2 = 1 - (1 / 4) ^ 2 := by linarith
    rw [this]
    norm_num
  have h3 : Real.cos (a + b) = Real.cos a * Real.cos b - Real.sin a * Real.sin b := Real.cos_add a b
  have h4 : Real.cos (a - b) = Real.cos a * Real.cos b + Real.sin a * Real.sin b := Real.cos_sub a b
  rw [h3, h4]
  have h5 : Real.cos a * Real.cos b = 1 / 12 := by
    rw [ha, hb]
    norm_num
  have h6 : (Real.sin a) ^ 2 * (Real.sin b) ^ 2 = 5 / 6 := by
    calc
      (Real.sin a) ^ 2 * (Real.sin b) ^ 2 = (8 / 9) * (15 / 16) := by rw [h1, h2]
      _ = (5 / 6) := by norm_num
  have eqn : (Real.cos a * Real.cos b - Real.sin a * Real.sin b) * (Real.cos a * Real.cos b + Real.sin a * Real.sin b) = (Real.cos a * Real.cos b) ^ 2 - (Real.sin a * Real.sin b) ^ 2 := by
    ring
  rw [eqn]
  have h7 : (Real.cos a * Real.cos b) ^ 2 = (1 / 12) ^ 2 := by
    rw [h5]
  have h8 : (Real.sin a * Real.sin b) ^ 2 = (5 / 6) := by
    calc
      (Real.sin a * Real.sin b) ^ 2 = (Real.sin a) ^ 2 * (Real.sin b) ^ 2 := by ring
      _ = (5 / 6) := h6
  rw [h7, h8]
  norm_num [h5]