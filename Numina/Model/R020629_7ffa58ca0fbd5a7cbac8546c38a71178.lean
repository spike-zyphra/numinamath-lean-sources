import Mathlib

theorem algebra_323363 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.sqrt a * (Real.sqrt a + 4 * Real.sqrt b) = 3 * Real.sqrt b * (Real.sqrt a + 2 * Real.sqrt b)) :
    (a + 6 * Real.sqrt (a * b) - 8 * b) / (2 * a - 3 * Real.sqrt (a * b) + 2 * b) = 2 := by
  have h1 : Real.sqrt a ^2 = a := by 
    exact Real.sq_sqrt (by linarith)
  have h2 : Real.sqrt b ^2 = b := by 
    exact Real.sq_sqrt (by linarith)
  have h4 : Real.sqrt a ^2 + Real.sqrt a * Real.sqrt b - 6 * (Real.sqrt b ^2) = 0 := by
    nlinarith 
  have h5 : Real.sqrt a = 2 * Real.sqrt b := by
    have h6 : Real.sqrt a ^2 + Real.sqrt a * Real.sqrt b - 6 * (Real.sqrt b ^2) = 0 := h4
    have h7 : Real.sqrt a - 2 * Real.sqrt b = 0 ∨ Real.sqrt a + 3 * Real.sqrt b = 0 := by
      have h8 : Real.sqrt a ^2 + Real.sqrt a * Real.sqrt b - 6 * (Real.sqrt b ^2) = 
          (Real.sqrt a - 2 * Real.sqrt b) * (Real.sqrt a + 3 * Real.sqrt b) := by 
        nlinarith
      rw [h8] at h6
      cases (mul_eq_zero.mp h6) with
      | inl h9 => 
        left
        linarith
      | inr h10 => 
        right
        linarith
    cases h7 with
    | inl h8 => 
      linarith 
    | inr h9 => 
      have h10 : Real.sqrt a + 3 * Real.sqrt b > 0 := by
        have h9 : Real.sqrt a > 0 := by 
          apply Real.sqrt_pos.mpr 
          linarith
        have h8 : Real.sqrt b > 0 := by 
          apply Real.sqrt_pos.mpr 
          linarith
        linarith 
      linarith 
  have h8 : a = 4 * b := by 
    have h7 : Real.sqrt a = 2 * Real.sqrt b := h5 
    have h9 : Real.sqrt a ^2 = 4 * (Real.sqrt b ^2) := by 
      nlinarith [h7]
    nlinarith [h1, h2]
  have h9 : Real.sqrt (a * b) = 2 * b := by 
    have h10 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by 
      rw [Real.sqrt_mul (by nlinarith)]
    rw [h10] 
    rw [show Real.sqrt a = 2 * Real.sqrt b by linarith [h5] ]
    have h11 : Real.sqrt b ^2 = b := h2 
    nlinarith 
  have h10 : a + 6 * Real.sqrt (a * b) - 8 * b = 8 * b := by 
    rw [h9] 
    nlinarith [h8] 
  have h11 : 2 * a - 3 * Real.sqrt (a * b) + 2 * b = 4 * b := by 
    rw [h9] 
    nlinarith [h8] 
  have hb2 : b ≠ 0 := by linarith 
  rw [h10, h11] 
  field_simp [hb2] 
  <;> nlinarith