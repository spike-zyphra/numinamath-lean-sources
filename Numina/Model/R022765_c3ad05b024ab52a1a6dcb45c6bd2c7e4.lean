import Mathlib

theorem algebra_217253 {x y : ℝ} (h₀ : x^2 + Real.sqrt 3 * y = 4) (h₁ : y^2 + Real.sqrt 3 * x = 4) (h₂ : x ≠ y) :
    y / x + x / y = -5 := by
  have h3 : (x - y) * (x + y - Real.sqrt 3) = 0 := by
    have eq1 : x^2 + Real.sqrt 3 * y = 4 := h₀
    have eq2 : y^2 + Real.sqrt 3 * x = 4 := h₁
    have eq3 : x^2 + Real.sqrt 3 * y - (y^2 + Real.sqrt 3 * x) = 0 := by
      linarith
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_pos_of_ne_zero (show x - y ≠ 0 by
      intro h
      apply h₂
      linarith
    ), sq_nonneg (x - y), sq_nonneg (x + y - Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case $x - y = 0$
    exfalso
    apply h₂
    linarith
  · -- Case $x + y - \sqrt{3} = 0$
    have h6 : x + y = Real.sqrt 3 := by linarith

    have h7 : x * y = -1 := by
      have eq1 : x^2 + Real.sqrt 3 * y = 4 := h₀
      have eq2 : y^2 + Real.sqrt 3 * x = 4 := h₁
      have h8 : x^2 + y^2 = 5 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_pos_of_ne_zero (show x - y ≠ 0 by
          intro h
          apply h₂
          linarith
        ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)), h6]
      have h9 : (x + y)^2 = 3 := by
        calc
          (x + y) ^ 2 = (Real.sqrt 3) ^2 := by rw [h6]
          _ = 3 := Real.sq_sqrt (by norm_num)
      have h10 : (x + y) ^ 2 = x^2 + y^2 + 2 * (x * y) := by ring
      nlinarith [h8, h9, h10]

    have hx1 : x ≠ 0 := by
      by_contra h
      have h0 : x = 0 := by linarith
      rw [h0] at h₀ h₁ h7
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (y - 0), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    
    have hy1 : y ≠ 0 := by
      by_contra h
      have h0 : y = 0 := by linarith
      rw [h0] at h₀ h₁ h7
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - 0), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    
    field_simp [hx1, hy1]
    nlinarith [h7, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - y), sq_pos_of_ne_zero (show x - y ≠ 0 by
      intro h
      apply h₂
      linarith
    )]