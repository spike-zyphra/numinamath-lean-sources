import Mathlib

theorem algebra_21152 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a^2 + b^2 = 49) (h' : 2^2 / a^2 - 12^2 / b^2 = 1) :
    a = 1 ∧ b = 4 * Real.sqrt 3 := by

  have h1 : a^2 + b^2 = 49 := h

  have eq1 : a^2 * b^2 + 144 * a^2 - 4 * b^2 = 0 := by
    field_simp [show 0 < a^2 by nlinarith, show 0 < b^2 by nlinarith] at h'
    nlinarith
  
  have eq2 : b^2 = 49 - a^2 := by
    linarith [h1]

  rw [eq2] at eq1
  
  have eq3 : a^4 - 197 * a^2 + 196 = 0 := by
    nlinarith
  
  have eq4 : (a^2 - 1) * (a^2 - 196) = 0 := by
    nlinarith [eq3]
  
  cases' (mul_eq_zero.mp eq4) with ha1 ha2
  
  · -- First case, where a^2 - 1 = 0
    have ha' : a^2 = 1 := by linarith
    have ha2 : a = 1 := by nlinarith [show 0 < a from ha]
    
    have hb' : b^2 = 48 := by
      nlinarith [h1, ha']
    
    have hb2 : b = 4 * Real.sqrt 3 := by
      have h3 : b^2 = 48 := hb'
      have hb4 : b > 0 := by linarith [hb]
      have : b = Real.sqrt (b ^ 2) := by
        rw [Real.sqrt_sq (by linarith)]
      rw [this]
      rw [h3]
      have h4 : Real.sqrt 48 = 4 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h4]
    
    exact ⟨ha2, hb2⟩
  
  · -- Second case, where a^2 - 196 = 0
    have ha' : a^2 = 196 := by linarith
    have h2 : b^2 = -147 := by nlinarith [h1, ha']
    nlinarith [show 0 < b from hb, show b^2 ≥ 0 from sq_nonneg b]