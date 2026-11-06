import Mathlib

theorem calculus_23444 {a b : ℝ × ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : (a.1 + b.1, a.2 + b.2) • b = 0)
    (h2 : (a.1 + 2 * b.1, a.2 + 2 * b.2) • a = 0) :
    Real.sqrt (a.1 ^ 2 + a.2 ^ 2) / Real.sqrt (b.1 ^ 2 + b.2 ^ 2) = Real.sqrt 2 := by 
  have eq1 : (a.1 + b.1) * b.1 + (a.2 + b.2) * b.2 = 0 := by
    simp [Prod.ext_iff, mul_add, add_mul] at h1 ⊢
    nlinarith
  have eq2 : (a.1 + 2 * b.1) * a.1 + (a.2 + 2 * b.2) * a.2 = 0 := by
    simp [Prod.ext_iff, mul_add, add_mul] at h2 ⊢
    nlinarith
  have eq3 : a.1 * b.1 + a.2 * b.2 + (b.1 ^ 2 + b.2 ^ 2) = 0 := by 
    nlinarith 
  have eq4 : a.1 * b.1 + a.2 * b.2 = - (b.1 ^ 2 + b.2 ^ 2) := by 
    linarith 
  have eq5 : a.1 ^ 2 + a.2 ^ 2 = 2 * (b.1 ^ 2 + b.2 ^ 2) := by 
    have h : a.1 ^ 2 + a.2 ^ 2 + 2 * (a.1 * b.1 + a.2 * b.2) = 0 := by 
      linarith [eq2]
    rw [show a.1 * b.1 + a.2 * b.2 = - (b.1 ^ 2 + b.2 ^ 2) by linarith [eq4]] at h 
    linarith 
  have hb2_pos : b.1 ^ 2 + b.2 ^ 2 > 0 := by 
    by_contra h 
    push_neg at h 
    have h4 : b.1 = 0 := by nlinarith [sq_nonneg (b.1), sq_nonneg (b.2)]
    have h5 : b.2 = 0 := by nlinarith [sq_nonneg (b.1), sq_nonneg (b.2)]
    have h6 : b = (0, 0) := by 
      simp [Prod.ext_iff, h4, h5]
    have h7 : b = 0 := by 
      simp [Prod.ext_iff] at h6 ⊢ 
      exact h6
    contradiction
  have h4 : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = Real.sqrt 2 * Real.sqrt (b.1 ^ 2 + b.2 ^ 2) := by 
    have h5 : a.1 ^ 2 + a.2 ^ 2 = 2 * (b.1 ^ 2 + b.2 ^ 2) := by linarith [eq5]
    have h7 : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = Real.sqrt (2 * (b.1 ^ 2 + b.2 ^ 2)) := by 
      rw [show 2 * (b.1 ^ 2 + b.2 ^ 2) = a.1 ^ 2 + a.2 ^ 2 by linarith [h5]]
    have h8 : Real.sqrt (2 * (b.1 ^ 2 + b.2 ^ 2)) = Real.sqrt (2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2) := by 
      rw [Real.sqrt_mul (by positivity)]
    rw [h7, h8]
  have h8 : Real.sqrt (b.1 ^ 2 + b.2 ^ 2) > 0 := by 
    have h9 : b.1 ^ 2 + b.2 ^ 2 > 0 := hb2_pos
    positivity 
  have h9 : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) / Real.sqrt (b.1 ^ 2 + b.2 ^ 2) = Real.sqrt 2 := by 
    rw [h4]
    field_simp [h8]
    <;> nlinarith 
  exact h9