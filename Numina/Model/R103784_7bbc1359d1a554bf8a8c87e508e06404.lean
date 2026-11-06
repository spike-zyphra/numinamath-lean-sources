import Mathlib

theorem algebra_308986 {a b c : ℝ} (h₀ : a + b = 8) (h₁ : a * b - c ^ 2 + 8 * Real.sqrt 2 * c = 48) :
    b * x ^ 2 + c * x - a = 0 ↔ x = (-Real.sqrt 2 + Real.sqrt 6) / 2 ∨ x = -(Real.sqrt 2 + Real.sqrt 6) / 2 := by

  have h2 : b = 8 - a := by linarith

  rw [h2] at h₁
  have h2' : (a - 4)^2 + (c - 4 * Real.sqrt 2)^2 = 0 := by
    have h_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h_sq_4 : (Real.sqrt 2) ^ 4 = 4 := by
      calc
        (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
        _ = (2) ^ 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        _ = 4 := by norm_num
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), sq_nonneg (a - 4), sq_nonneg (c - 4 * Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  
  have ha1 : (a - 4)^2 = 0 := by
    linarith [sq_nonneg (a - 4), sq_nonneg (c - 4 * Real.sqrt 2)]
  
  have ha : a = 4 := by
    nlinarith
  
  have hb : b = 4 := by 
    linarith

  have hc1 : (c - 4 * Real.sqrt 2)^2 = 0 := by
    linarith [sq_nonneg (a - 4), sq_nonneg (c - 4 * Real.sqrt 2)]

  have hc : c = 4 * Real.sqrt 2 := by 
    nlinarith

  rw [hb, ha, hc]
  constructor
  · -- Assume b * x^2 + c * x - a = 0
    intro h
    have h_eq : 4 * x ^ 2 + 4 * Real.sqrt 2 * x - 4 = 0 := by
      nlinarith

    have h_eq2 : x ^ 2 + Real.sqrt 2 * x - 1 = 0 := by
      nlinarith

    have h_d : x ^ 2 + Real.sqrt 2 * x - 1 = (x - (-Real.sqrt 2 + Real.sqrt 6) / 2) * (x - (-Real.sqrt 2 - Real.sqrt 6) / 2) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num : (6 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (x + Real.sqrt 2 / 2)]

    rw [h_d] at h_eq2

    cases' (mul_eq_zero.1 h_eq2) with h_eq_left h_eq_right
    · -- First factor is zero
      left
      linarith

    · -- Second factor is zero
      right
      nlinarith

  · -- Show that the roots satisfy the quadratic equation
    rintro (h | h)
    · -- First root
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num : (6 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 6)]

    · -- Second root
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num : (6 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 + Real.sqrt 6)]