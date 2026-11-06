import Mathlib

theorem algebra_328313 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : 1 / a + 1 / b = 1)
    (M N : ℝ) (hM : M = b / a + a / b) (hN : N = b / a ^ 2 + a / b ^ 2) :
    M > N := by

  have h1 : a + b = a * b := by
    field_simp [ha, hb] at h 
    linarith
  
  have hM1 : M = (a * b) - 2 := by
    rw [hM]
    have eq1 : b / a + a / b = (b ^ 2 + a ^ 2) / (a * b) := by
      field_simp [ha, hb]
      <;> ring 
    have eq2 : b ^ 2 + a ^ 2 = (a * b) ^ 2 - 2 * (a * b) := by
      have eq3 : a + b = a * b := h1
      have eq4 : (a + b) ^ 2 = (a * b) ^ 2 := by
        rw [eq3]
      have eq5 : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by
        ring 
      nlinarith 
    rw [eq1]
    have eq4 : a * b ≠ 0 := by 
      apply mul_ne_zero 
      exact ha 
      exact hb 
    field_simp [eq4] 
    nlinarith [eq2]

  have hN1 : N = (a * b) - 3 := by
    rw [hN]
    have eq1 : b / a ^ 2 + a / b ^ 2 = (b ^ 3 + a ^ 3) / (a ^ 2 * b ^ 2) := by 
      field_simp [ha, hb]
      <;> ring 
    have eq2 : b ^ 3 + a ^ 3 = (a * b) ^ 3 - 3 * (a * b) ^ 2 := by
      have eq3 : a + b = a * b := h1 
      calc 
        b ^ 3 + a ^ 3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by 
          ring_nf 
        _ = (a * b) ^ 3 - 3 * (a * b) * (a * b) := by 
          rw [eq3] 
        _ = (a * b) ^ 3 - 3 * (a * b) ^ 2 := by 
          ring
    rw [eq1]
    have eq4 : a ^ 2 * b ^ 2 ≠ 0 := by
      apply mul_ne_zero 
      · -- Show a ^ 2 ≠ 0 
        apply pow_ne_zero 2 
        exact ha 
      · -- Show b ^ 2 ≠ 0 
        apply pow_ne_zero 2 
        exact hb 
    have eq5 : (a ^ 2 * b ^ 2) = (a * b) ^ 2 := by 
      ring 
    rw [eq5] 
    field_simp [show (a * b) ≠ 0 by apply mul_ne_zero ha hb] 
    nlinarith [eq2]

  rw [hM1, hN1] 
  linarith