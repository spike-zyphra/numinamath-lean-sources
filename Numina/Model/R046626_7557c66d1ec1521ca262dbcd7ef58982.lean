import Mathlib

theorem algebra_303169 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hA : A ≠ B) (hB : B ≠ C) (hC : A ≠ C) (h₁ : Real.sin C ≠ 0) (h₂ : Real.cos C ≠ 0)
    (h₃ : a * Real.sin A + b * Real.sin B + c * Real.sin C = 0) (h₄ : a * Real.cos A + b * Real.cos B + c * Real.cos C = 0) :
    Real.sin (B - C) / a = Real.sin (C - A) / b ∧ Real.sin (C - A) / b = Real.sin (A - B) / c := by

  have eq1 : b * Real.sin (B - C) = a * Real.sin (C - A) := by
    have h5 : Real.sin (B - C) = Real.sin B * Real.cos C - Real.cos B * Real.sin C := by
      rw [Real.sin_sub]
    have h6 : Real.sin (C - A) = Real.sin C * Real.cos A - Real.cos C * Real.sin A := by
      rw [Real.sin_sub]
    rw [h5, h6]
    have eq2 : a * (Real.sin A * Real.cos C - Real.cos A * Real.sin C) + b * (Real.sin B * Real.cos C - Real.cos B * Real.sin C) = 0 := by
      have eq3 : a * Real.sin A * Real.cos C + b * Real.sin B * Real.cos C + c * Real.sin C * Real.cos C = 0 := by
        have h7 : a * Real.sin A + b * Real.sin B + c * Real.sin C = 0 := h₃
        have h8 : Real.cos C ≠ 0 := h₂
        have h9 : a * Real.sin A * Real.cos C + b * Real.sin B * Real.cos C + c * Real.sin C * Real.cos C = (a * Real.sin A + b * Real.sin B + c * Real.sin C) * Real.cos C := by
          ring
        rw [h9]
        rw [h7]
        norm_num
      have eq4 : a * Real.cos A * Real.sin C + b * Real.cos B * Real.sin C + c * Real.cos C * Real.sin C = 0 := by
        have h7 : a * Real.cos A + b * Real.cos B + c * Real.cos C = 0 := h₄
        have h8 : Real.sin C ≠ 0 := by
          exact h₁
        have h9 : a * Real.cos A * Real.sin C + b * Real.cos B * Real.sin C + c * Real.cos C * Real.sin C = (a * Real.cos A + b * Real.cos B + c * Real.cos C) * Real.sin C := by
          ring
        rw [h9]
        rw [h7]
        norm_num
      nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C]
    linarith

  have eq2 : c * Real.sin (C - A) = b * Real.sin (A - B) := by
    have h7 : Real.sin (C - A) = Real.sin C * Real.cos A - Real.cos C * Real.sin A := by
      rw [Real.sin_sub]
    have h8 : Real.sin (A - B) = Real.sin A * Real.cos B - Real.cos A * Real.sin B := by
      rw [Real.sin_sub]
    rw [h7, h8]
    have eq3 : b * (Real.sin B * Real.cos A - Real.cos B * Real.sin A) + c * (Real.sin C * Real.cos A - Real.cos C * Real.sin A) = 0 := by
      have eq4 : a * Real.sin A * Real.cos A + b * Real.sin B * Real.cos A + c * Real.sin C * Real.cos A = 0 := by
        have h7 : a * Real.sin A + b * Real.sin B + c * Real.sin C = 0 := h₃
        have h8 : Real.cos A = Real.cos A := by rfl
        have h9 : a * Real.sin A * Real.cos A + b * Real.sin B * Real.cos A + c * Real.sin C * Real.cos A = (a * Real.sin A + b * Real.sin B + c * Real.sin C) * Real.cos A := by
          ring
        rw [h9]
        rw [h7]
        norm_num
      have eq5 : a * Real.cos A * Real.sin A + b * Real.cos B * Real.sin A + c * Real.cos C * Real.sin A = 0 := by
        have h4 : a * Real.cos A + b * Real.cos B + c * Real.cos C = 0 := h₄
        have h11 : Real.sin A = Real.sin A := by rfl
        have h9 : a * Real.cos A * Real.sin A + b * Real.cos B * Real.sin A + c * Real.cos C * Real.sin A = (a * Real.cos A + b * Real.cos B + c * Real.cos C) * Real.sin A := by
          ring
        rw [h9]
        rw [h4]
        norm_num
      nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C]
    linarith

  constructor
  · -- Show $\frac{\sin (B - C)}{a} = \frac{\sin (C - A)}{b}$.
    have h3 : Real.sin (B - C) / a = Real.sin (C - A) / b := by
      have h4 : b * Real.sin (B - C) = a * Real.sin (C - A) := eq1
      field_simp [ha, hb]
      linarith
    exact h3
  · -- Show $\frac{\sin (C - A)}{b} = \frac{\sin (A - B)}{c}$.
    have h3 : Real.sin (C - A) / b = Real.sin (A - B) / c := by
      have h4 : c * Real.sin (C - A) = b * Real.sin (A - B) := eq2
      field_simp [hb, hc]
      linarith
    exact h3