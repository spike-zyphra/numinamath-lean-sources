import Mathlib

theorem algebra_148463 (a b : ℝ) (h : ∀ x, 8 * 2 ^ x = (16 : ℝ) ^ ((1 : ℝ) / x) ↔
    x ^ 4 - 3 * x ^ 3 + a * x ^ 2 + 51 * x + b = 0) :
    a = -13 ∧ b = -36 ∧ (3 ^ 4 - 3 * 3 ^ 3 + a * 3 ^ 2 + 51 * 3 + b = 0) ∧
    (3 ^ 4 - 3 * 3 ^ 3 + a * 3 ^ 2 + 51 * 3 + b = 0) := by

  have h1 := h 1
  norm_num at h1

  have h2 := h (-4)
  have h16 : (16 : ℝ) ^ (-(1 / 4) : ℝ) = 1 / 2 := by
    have h1 : (16 : ℝ) ^ (-(1 / 4) : ℝ) = (2 ^ (4 : ℝ)) ^ (-(1 / 4) : ℝ) := by norm_num
    rw [h1]
    have h2 : ((2 : ℝ) ^ (4 : ℝ)) ^ (-(1 / 4) : ℝ) = (2 : ℝ) ^ (4 * (-(1 / 4) : ℝ)) := by
      rw [← Real.rpow_mul]
      all_goals norm_num
    rw [h2]
    have h3 : (4 : ℝ) * (-(1 / 4) : ℝ) = (-1 : ℝ) := by norm_num
    rw [h3]
    have h4 : (2 : ℝ) ^ (-1 : ℝ) = (1 / 2 : ℝ) := by 
      rw [Real.rpow_neg, Real.rpow_one]
      all_goals norm_num
    rw [h4]

  norm_num [h16] at h2
  ring_nf at h2
  
  have eq1 : a + b = -49 := by linarith

  have eq2 : ( -4 : ℝ ) ^ 4 - 3 * ( -4 : ℝ ) ^ 3 + a * ( -4 : ℝ ) ^ 2 + 51 * ( -4 ) + b = 0 := by linarith [h2]

  ring_nf at eq2
  have eq3 : 16 * a + b = -244 := by 
    nlinarith
  
  have ha : a = -13 := by 
    linarith [eq1, eq3]

  have hb : b = -36 := by 
    linarith [ha, eq1]

  constructor
  · exact ha
  constructor
  · exact hb
  constructor
  · 
    rw [ha, hb]
    norm_num
  · 
    rw [ha, hb]
    norm_num