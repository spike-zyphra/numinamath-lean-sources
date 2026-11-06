import Mathlib

theorem algebra_21953 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ x : ℝ, x^2 + a * x + b = 0 ↔ x = a ∨ x = b) : (a, b) = (1, -2) := by 
  -- a is a root
  have h₁ := h a
  simp at h₁ 
  -- b is a root
  have h₂ := h b
  simp at h₂ 
  -- From $a$ being a root we have $2a^2 + b = 0$
  have eq1 : b = -2 * a^2 := by 
    nlinarith
  -- From $b$ being a root we have $b^2 + a * b + b = 0$
  have eq3 : b + a + 1 = 0 := by 
    have h5 : b * (b + a + 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Contradiction if b = 0
      contradiction 
    · -- Therefore, b + a + 1 = 0
      linarith 
  -- Now we solve the system of equations 
  have eq4 : b = -a - 1 := by linarith 
  have eq6 : -2 * a^2 = -a - 1 := by 
    linarith [eq1, eq4] 
  have eq7 : 2 * a^2 - a - 1 = 0 := by 
    nlinarith 
  have h8 : (a - 1) * (2 * a + 1) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp h8) with h9 h10 
  · -- Case a = 1
    have ha1 : a = 1 := by linarith 
    have hb1 : b = -2 := by 
      rw [ha1] at eq4 
      linarith 
    exact Prod.ext ha1 hb1 
  · -- Case a = -1/2 
    have ha2 : a = -1 / 2 := by linarith 
    have hb2 : b = -1 / 2 := by 
      rw [ha2] at eq4 
      linarith 
    -- Contradiction: $1$ should be a root 
    have h3 := h 1 
    norm_num [ha2, hb2] at h3 
    all_goals linarith