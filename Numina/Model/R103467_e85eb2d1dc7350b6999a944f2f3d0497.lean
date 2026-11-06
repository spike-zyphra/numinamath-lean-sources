import Mathlib

theorem algebra_220370 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h : a / 2017 + 2017 / a = b / 2017 + 2017 / b) :
    Real.sqrt (a * b) = 2017 := by
  have h1 : a * b = 2017 ^ 2 := by 
    have h2 : a / 2017 + 2017 / a = b / 2017 + 2017 / b := h
    field_simp [ha, hb] at h2 ⊢
    have h4 : (a - b) * (a * b - 2017 ^ 2) = 0 := by 
      nlinarith [h2]
    cases (mul_eq_zero.mp h4) with
    | inl h6 =>
      exfalso
      apply hab 
      linarith
    | inr h7 =>
      linarith
  have h3 : Real.sqrt (a * b) = 2017 := by 
    rw [h1]
    rw [Real.sqrt_sq (by norm_num)]
  exact h3