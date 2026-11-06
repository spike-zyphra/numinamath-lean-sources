import Mathlib

theorem algebra_249178 {a b c d a' b' c' d' : ℝ} (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c) (h₃ : 0 < d)
    (h₄ : 0 < a') (h₅ : 0 < b') (h₆ : 0 < c') (h₇ : 0 < d') (h₈ : a / a' = b / b') (h₉ : b / b' = c / c')
    (h₁₀ : c / c' = d / d') :
    Real.sqrt (a * a') + Real.sqrt (b * b') + Real.sqrt (c * c') + Real.sqrt (d * d') =
    Real.sqrt ((a + b + c + d) * (a' + b' + c' + d')) := by 
  have h13 : a * b' = b * a' := by
    have h14 : a' ≠ 0 := by linarith
    have h15 : b' ≠ 0 := by linarith
    field_simp [h14, h15] at h₈ ⊢
    <;> nlinarith
  have h14 : b * c' = c * b' := by 
    have h16 : b' ≠ 0 := by linarith
    have h17 : c' ≠ 0 := by linarith
    field_simp [h16, h17] at h₉ ⊢
    <;> nlinarith
  have h15 : c * d' = d * c' := by
    have h18 : c' ≠ 0 := by linarith
    have h19 : d' ≠ 0 := by linarith
    field_simp [h18, h19] at h₁₀ ⊢
    <;> nlinarith
  have h21 : a = (a / a') * a' := by
    field_simp [show 0 < a' from h₄]
  have h22 : b = (a / a') * b' := by 
    have h23 : a / a' = b / b' := h₈
    have h24 : 0 < b' := h₅
    field_simp [h24] at h23 ⊢
    <;> nlinarith
  have h23 : c = (a / a') * c' := by
    have h24 : a / a' = c / c' := by
      linarith [h₈, h₉]
    have h25 : 0 < c' := h₆
    field_simp [h25] at h24 ⊢
    <;> nlinarith
  have h24 : d = (a / a') * d' := by
    have h25 : a / a' = d / d' := by
      linarith [h₈, h₉, h₁₀]
    have h26 : 0 < d' := h₇
    field_simp [h26] at h25 ⊢
    <;> nlinarith
  have h26 : Real.sqrt (a * a') = Real.sqrt (a / a') * a' := by
    have h27 : a * a' = (a / a') * (a' ^ 2) := by
      field_simp [show 0 < a' from h₄]
      <;> nlinarith
    rw [h27]
    have h28 : 0 ≤ a' := by linarith
    have h29 : Real.sqrt ((a / a') * (a' ^ 2)) = Real.sqrt (a / a') * Real.sqrt (a' ^ 2) := by 
      rw [Real.sqrt_mul (by positivity)]
    rw [h29]
    have h30 : Real.sqrt (a' ^ 2) = a' := by
      rw [Real.sqrt_sq (by linarith)]
    rw [h30]
  have h27 : Real.sqrt (b * b') = Real.sqrt (a / a') * b' := by 
    have h28 : b * b' = (a / a') * (b' ^ 2) := by
      have h29 : a / a' = b / b' := h₈
      field_simp [show 0 < b' from h₅] at h29 ⊢
      <;> nlinarith
    rw [h28]
    have h30 : 0 ≤ b' := by linarith
    have h31 : Real.sqrt ((a / a') * (b' ^ 2)) = Real.sqrt (a / a') * Real.sqrt (b' ^ 2) := by 
      rw [Real.sqrt_mul (by positivity)]
    rw [h31]
    have h32 : Real.sqrt (b' ^ 2) = b' := by
      rw [Real.sqrt_sq (by linarith)]
    rw [h32]
  have h28 : Real.sqrt (c * c') = Real.sqrt (a / a') * c' := by 
    have h29 : c * c' = (a / a') * (c' ^ 2) := by
      have h30 : a / a' = c / c' := by 
        linarith [h₈, h₉]
      field_simp [show 0 < c' from h₆] at h30 ⊢
      <;> nlinarith
    rw [h29]
    have h31 : 0 ≤ c' := by linarith
    have h32 : Real.sqrt ((a / a') * (c' ^ 2)) = Real.sqrt (a / a') * Real.sqrt (c' ^ 2) := by 
      rw [Real.sqrt_mul (by positivity)]
    rw [h32]
    have h33 : Real.sqrt (c' ^ 2) = c' := by
      rw [Real.sqrt_sq (by linarith)]
    rw [h33]
  have h29 : Real.sqrt (d * d') = Real.sqrt (a / a') * d' := by 
    have h30 : d * d' = (a / a') * (d' ^ 2) := by 
      have h31 : a / a' = d / d' := by 
        linarith [h₈, h₉, h₁₀]
      field_simp [show 0 < d' from h₇] at h31 ⊢
      <;> nlinarith
    rw [h30]
    have h32 : 0 ≤ d' := by linarith
    have h33 : Real.sqrt ((a / a') * (d' ^ 2)) = Real.sqrt (a / a') * Real.sqrt (d' ^ 2) := by 
      rw [Real.sqrt_mul (by positivity)]
    rw [h33]
    have h34 : Real.sqrt (d' ^ 2) = d' := by 
      rw [Real.sqrt_sq (by linarith)]
    rw [h34]
  rw [h26, h27, h28, h29]
  have h33 : Real.sqrt (a / a') * a' + Real.sqrt (a / a') * b' + Real.sqrt (a / a') * c' + Real.sqrt (a / a') * d' = 
    Real.sqrt ((a + b + c + d) * (a' + b' + c' + d')) := by 
    have h34 : Real.sqrt (a / a') * a' + Real.sqrt (a / a') * b' + Real.sqrt (a / a') * c' + Real.sqrt (a / a') * d' = 
      Real.sqrt (a / a') * (a' + b' + c' + d') := by 
      ring
    rw [h34]
    have h35 : (a + b + c + d) * (a' + b' + c' + d') = (a / a') * (a' + b' + c' + d') ^ 2 := by 
      rw [show a = (a / a') * a' by linarith [h21]]
      rw [show b = (a / a') * b' by linarith [h22]]
      rw [show c = (a / a') * c' by linarith [h23]]
      rw [show d = (a / a') * d' by linarith [h24]]
      field_simp [show 0 < a' by linarith]
      <;> nlinarith
    rw [h35]
    have h36 : Real.sqrt ((a / a') * (a' + b' + c' + d') ^ 2) = Real.sqrt (a / a') * (a' + b' + c' + d') := by
      have h37 : Real.sqrt ((a / a') * (a' + b' + c' + d') ^ 2) = Real.sqrt (a / a') * Real.sqrt ((a' + b' + c' + d') ^ 2) := by 
        rw [Real.sqrt_mul (by positivity)]
      rw [h37]
      have h38 : Real.sqrt ((a' + b' + c' + d') ^ 2) = (a' + b' + c' + d') := by 
        rw [Real.sqrt_sq (by positivity)]
      rw [h38]
    rw [h36]
  linarith