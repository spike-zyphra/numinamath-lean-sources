import Mathlib

open Real


theorem algebra_213623 {x y : ℝ} (hx : 0 < x ∧ x ≠ 1) (hy : 0 < y ∧ y ≠ 1)
    (h1 : logb y x - 2 * logb x y = 1) (h2 : x - y = 2) :
    x = 4 ∧ y = 2 ∨ x = sqrt 2 + 1 ∧ y = sqrt 2 - 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have h5 : log x ≠ 0 := by
    have hx6 : x > 0 := hx0
    have hx7 : x ≠ 1 := hx1
    exact log_ne_zero_of_pos_of_ne_one hx6 hx7
  have h6 : log y ≠ 0 := by
    have hy7 : y > 0 := hy0
    have hy8 : y ≠ 1 := hy1
    exact log_ne_zero_of_pos_of_ne_one hy7 hy8
  have h3 : logb y x = (log x) / (log y) := by 
    field_simp [logb]
  have h4 : logb x y = (log y) / (log x) := by 
    field_simp [logb]
  rw [h3, h4] at h1
  have h7 : (log x) ^ 2 - (log x * log y) - 2 * (log y) ^ 2 = 0 := by
    field_simp [h6, h5] at h1 ⊢
    nlinarith
  have h7' : (log x - 2 * log y) * (log x + log y) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h7') with h8 h9
  · -- Case where $\ln x - 2 \ln y = 0$
    have h10 : log x = 2 * log y := by linarith
    have h11 : x = y ^ 2 := by
      have h12 : log x = log (y ^ 2) := by
        rw [h10]
        have h13 : log (y ^ 2) = 2 * log y := by
          simp [log_pow]
        linarith
      have h14 : x > 0 := hx0
      have h15 : y ^ 2 > 0 := by nlinarith
      exact log_injOn_pos (Set.mem_Ioi.mpr h14) (Set.mem_Ioi.mpr h15) h12
    have h12 : x = y + 2 := by linarith
    rw [show x = y ^ 2 by linarith] at h12
    have h13 : y ^ 2 - y - 2 = 0 := by
      nlinarith
    have h14 : (y - 2) * (y + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h14) with h15 h16
    · -- Case where $y = 2$
      have hy2 : y = 2 := by linarith
      have hx4 : x = 4 := by
        nlinarith
      left
      exact ⟨hx4, hy2⟩
    · -- Case where $y = -1$, which contradicts $y > 0$
      nlinarith
  · -- Case where $\ln x + \ln y = 0$
    have h10 : log x = - log y := by linarith
    have h11 : x = (1 / y) := by
      have h12 : log x = log (1 / y) := by 
        rw [h10]
        have h13 : log (1 / y) = - log y := by 
          simp [log_div, log_one]
        linarith 
      have h14 : x > 0 := hx0 
      have h15 : (1 / y) > 0 := by 
        positivity 
      exact log_injOn_pos (Set.mem_Ioi.mpr h14) (Set.mem_Ioi.mpr h15) h12
    have h12 : x = y + 2 := by linarith
    rw [h11] at h12
    have h13 : y^2 + 2*y - 1 = 0 := by
      field_simp [(show y ≠ 0 by linarith)] at h12 
      nlinarith 
    have h15 : (y - (-1 + Real.sqrt 2)) * (y - (-1 - Real.sqrt 2)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    cases' (mul_eq_zero.mp h15) with h16 h17
    · -- Case where $y = -1 + \sqrt{2}$
      have hy3 : y = Real.sqrt 2 - 1 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hx5 : x = Real.sqrt 2 + 1 := by
        rw [show x = 1 / y by linarith [h11]]
        rw [hy3]
        field_simp [(show (Real.sqrt 2 - 1 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        )]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      right
      exact ⟨hx5, hy3⟩
    · -- Case where $y = -1 - \sqrt{2} < 0$, which contradicts $0 < y$
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]