import Mathlib

theorem algebra_93031 {a b c x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : (a + b - c) / c = (a - b + c) / b) (h2 : (a - b + c) / b = (-a + b + c) / a)
    (hx : x = ((a + b) * (b + c) * (c + a)) / (a * b * c)) (hx1 : x < 0) : x = -1 := by
  have eq1 : b * (a + b - c) = c * (a - b + c) := by 
    have h1' : (a + b - c) / c = (a - b + c) / b := h1
    field_simp [hc, hb] at h1' ⊢
    linarith
  have eq2 : a * (a - b + c) = b * (-a + b + c) := by 
    have h2' : (a - b + c) / b = (-a + b + c) / a := h2
    field_simp [hb, ha] at h2' ⊢
    linarith
  have eq1' : (b - c) * (a + b + c) = 0 := by
    nlinarith 
  have eq2' : (a - b) * (a + b + c) = 0 := by 
    nlinarith 
  by_cases h : a + b + c = 0 
  · -- Assume $a + b + c = 0$, prove $x = -1$
    have hx2 : x = -1 := by 
      rw [hx]
      have h3 : a + b = -c := by linarith 
      have h4 : b + c = -a := by linarith 
      have h5 : c + a = -b := by linarith 
      calc 
        ((a + b) * (b + c) * (c + a)) / (a * b * c)
            = ((-c) * (-a) * (-b)) / (a * b * c) := by rw [h3, h4, h5]
        _ = (- (a * b * c)) / (a * b * c) := by ring_nf 
        _ = -1 := by
          have h6 : a * b * c ≠ 0 := by 
            apply mul_ne_zero 
            apply mul_ne_zero 
            exact ha 
            exact hb 
            exact hc 
          field_simp [h6] 
          <;> nlinarith
    linarith 
  · -- Assume $a + b + c ≠ 0$, derive a contradiction 
    have h3 : b - c = 0 := by 
      cases (mul_eq_zero.mp eq1') with 
      | inl h4 => linarith 
      | inr h5 => 
        exfalso 
        apply h 
        linarith 
    have h4 : a - b = 0 := by 
      cases (mul_eq_zero.mp eq2') with 
      | inl h5 => linarith 
      | inr h6 => 
        exfalso 
        apply h 
        linarith 
    have h5 : b = c := by linarith 
    have h6 : a = b := by linarith 
    have h7 : a = b := h6 
    have h8 : b = c := h5 
    have h9 : a = c := by linarith [h7, h8] 
    have hx2 : x = 8 := by 
      rw [hx] 
      have h10 : a * b * c ≠ 0 := by 
        apply mul_ne_zero 
        apply mul_ne_zero 
        exact ha 
        exact hb 
        exact hc 
      have h11 : a = c := h9 
      rw [show b = a by linarith [h7]] 
      rw [show c = a by linarith [h9]] 
      field_simp [show a ≠ 0 by assumption] 
      <;> 
        nlinarith 
    nlinarith