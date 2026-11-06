import Mathlib

theorem algebra_302674 {x : ℝ} (hx : x^2 + x + 1 = 2 / (x^2 + x)) :
    x = (-1 + Real.sqrt 5) / 2 ∨ x = (-1 - Real.sqrt 5) / 2 := by

  have h1 : x^2 + x ≠ 0 := by
    by_contra h
    have h2 : 2 / (x^2 + x) = 0 := by 
      rw [h]
      norm_num
    have h3 : x^2 + x + 1 = 0 := by linarith [hx, h2]
    have h4 : x^2 + x = 0 := by linarith
    nlinarith

  have eq1 : (x^2 + x + 1) * (x^2 + x) = 2 := by 
    have h2 : x^2 + x ≠ 0 := h1 
    field_simp [h2] at hx ⊢
    linarith 

  have eq2 : (x^2 + x - 1) * (x^2 + x + 2) = 0 := by 
    nlinarith [sq_nonneg (x^2 + x), sq_nonneg (x + 1/2)]

  cases' (mul_eq_zero.mp eq2) with h3 h4

  · -- Case $x^2 + x - 1 = 0$
    have eq3 : x^2 + x - 1 = 0 := by linarith 
    have h6 : (x + 1/2)^2 = 5/4 := by 
      nlinarith 

    have h7 : x + 1/2 = Real.sqrt 5 / 2 ∨ x + 1/2 = -Real.sqrt 5 / 2 := by 
      have h8 : (x + 1/2)^2 = 5/4 := h6 
      have h9 : (x + 1/2)^2 - 5/4 = 0 := by linarith 
      have h10 : (x + 1/2 - Real.sqrt 5 / 2) * (x + 1/2 + Real.sqrt 5 / 2) = 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- Case $x + \frac{1}{2} - \frac{\sqrt{5}}{2} = 0$
        left 
        linarith 
      · -- Case $x + \frac{1}{2} + \frac{\sqrt{5}}{2} = 0$
        right 
        linarith 
    cases' h7 with h7 h7
    · -- Case $x + \frac{1}{2} = \frac{\sqrt{5}}{2}$
      left 
      linarith 
    · -- Case $x + \frac{1}{2} = -\frac{\sqrt{5}}{2}$
      right 
      linarith 

  · -- Case $x^2 + x + 2 = 0$
    have eq4 : x^2 + x + 2 = 0 := by linarith 
    nlinarith [sq_nonneg (x + 1/2)]