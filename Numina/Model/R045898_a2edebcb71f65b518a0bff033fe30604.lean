import Mathlib

theorem inequalities_69009 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (b * c) + 1 / (c * a) + 1 / (a * b) ≥ 1) :
    1 ≤ a / (b * c) + b / (c * a) + c / (a * b) := by
  have h₁ : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : a + b + c ≥ a * b * c := by
    have h3 : 1 / (b * c) + 1 / (c * a) + 1 / (a * b) = (a + b + c) / (a * b * c) := by 
      field_simp
      ring
    rw [h3] at h 
    have h4 : (a + b + c) / (a * b * c) ≥ 1 := by linarith 
    have h5 : (a + b + c) ≥ a * b * c := by
      have h6 : (a * b * c) > 0 := h₁
      apply (le_div_iff₀ h6).mp at h4
      linarith
    linarith
  have h3 : a / (b * c) + b / (c * a) + c / (a * b) = (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) := by
    field_simp
    ring
  rw [h3]
  have h4 : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) ≥ 1 := by
    have h5 : (a ^ 2 + b ^ 2 + c ^ 2) ≥ a * b * c := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
        sq_nonneg (a + b + c - a * b * c), h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc 
      ]
    have h6 : a * b * c > 0 := h₁
    apply (le_div_iff₀ h6).mpr
    linarith
  linarith