import Mathlib

theorem algebra_279943 {a b c p q : ℝ} (ha : a^3 + p * a + q = 0) (hb : b^3 + p * b + q = 0)
    (hc : c^3 + p * c + q = 0) (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) : a + b + c = 0 := by

  have eq1 : a^2 + a * b + b^2 + p = 0 := by 
    have eq2 : a^3 + p * a + q - (b^3 + p * b + q) = 0 := by
      linarith [ha, hb]
    have eq3 : a^3 - b^3 + p * a - p * b = 0 := by
      linarith [eq2]
    have eq4 : (a - b) * (a^2 + a * b + b^2 + p) = 0 := by
      ring_nf at eq3 ⊢
      linarith
    cases' (mul_eq_zero.mp eq4) with h1 h2
    · -- $a - b = 0$, so $a = b$ which contradicts $a \neq b$
      exfalso
      apply habc.1
      linarith
    · -- $a^2 + a * b + b^2 + p = 0$
      linarith

  have eq2 : b^2 + b * c + c^2 + p = 0 := by 
    have eq3 : b^3 + p * b + q - (c^3 + p * c + q) = 0 := by
      linarith [hb, hc]
    have eq4 : b^3 - c^3 + p * b - p * c = 0 := by
      linarith [eq3]
    have eq5 : (b - c) * (b^2 + b * c + c^2 + p) = 0 := by
      ring_nf at eq4 ⊢
      linarith
    cases' (mul_eq_zero.mp eq5) with h1 h2
    · -- $b - c = 0$, which contradicts $b \neq c$
      exfalso
      apply habc.2.2
      linarith
    · -- $b^2 + b * c + c^2 + p = 0$
      linarith
  
  have eq3 : (a - c) * (a + b + c) = 0 := by 
    nlinarith [eq1, eq2]

  cases' (mul_eq_zero.mp eq3) with h1 h2
  · -- $a - c = 0$, which contradicts $a \neq c$
    exfalso
    apply habc.2.1
    linarith
  · -- $a + b + c = 0$
    linarith