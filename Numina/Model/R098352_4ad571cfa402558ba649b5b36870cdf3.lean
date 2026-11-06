import Mathlib

theorem algebra_301733 {p q : ℝ} (a b : ℝ) (ha : a > 1) (hb : b < 1)
    (h : -a^2 + p * a + q = 0 ∧ -b^2 + p * b + q = 0) : p + q > 1 := by
        have h₁ : -a^2 + p * a + q = 0 := h.1
        have h₂ : -b^2 + p * b + q = 0 := h.2
        have eq1 : p = a + b := by 
            have eq1 : -a^2 + p * a + q - (-b^2 + p * b + q) = 0 := by linarith
            have eq2 : (a - b) * (p - (a + b)) = 0 := by
                nlinarith [eq1]
            cases' (mul_eq_zero.mp eq2) with h₃ h₄
            · -- Case $a - b = 0$, which is impossible because $a > 1 > b$
              nlinarith
            · -- Case $p - (a + b) = 0$, so $p = a + b$
              linarith
        have eq2 : q = -a * b := by 
            rw [eq1] at h₁ 
            nlinarith 
        rw [eq1, eq2]
        nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr (show 1 - b > 0 by linarith))]