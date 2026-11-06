import Mathlib

theorem algebra_108881 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a^2 + b^2 - 2 * a * Real.sqrt 2 - 2 * b * Real.sqrt 3 + 5 = 0) :
    (2 / a + 3 / b) * (b - a) = 1 := by 
  have h1 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  
  have h_eq : (a - Real.sqrt 2) ^ 2 + (b - Real.sqrt 3) ^ 2 = 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, h, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  have h_a : (a - Real.sqrt 2) ^ 2 = 0 := by
    linarith [sq_nonneg (a - Real.sqrt 2), sq_nonneg (b - Real.sqrt 3)]
  
  have h_b : (b - Real.sqrt 3) ^ 2 = 0 := by
    linarith [sq_nonneg (a - Real.sqrt 2), sq_nonneg (b - Real.sqrt 3)]
  
  have ha_eq : a = Real.sqrt 2 := by 
    nlinarith
  
  have hb_eq : b = Real.sqrt 3 := by 
    nlinarith
  
  -- Simplify 2/a as sqrt(2)
  have h3 : 2 / a = Real.sqrt 2 := by
    rw [ha_eq]
    have h4 : Real.sqrt 2 ≠ 0 := by positivity 
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  -- Simplify 3/b as sqrt(3)
  have h5 : 3 / b = Real.sqrt 3 := by
    rw [hb_eq]
    have h6 : Real.sqrt 3 ≠ 0 := by positivity 
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
  have h7 : (2 / a + 3 / b) * (b - a) = 1 := by
    rw [h3, h5, ha_eq, hb_eq]

    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    ]
  
  exact h7