import Mathlib

open Real

theorem algebra_11508 (x : ℝ) (hx : x ≥ 8) :
    6 / (sqrt (x - 8) - 9) + 1 / (sqrt (x - 8) - 4) +
    7 / (sqrt (x - 8) + 4) + 12 / (sqrt (x - 8) + 9) = 0 ↔ x = 17 ∨ x = 44 := by
  constructor
  · -- Assume the equation holds, prove x = 17 or x = 44
    intro h_eq
    have h1 : 0 ≤ sqrt (x - 8) := Real.sqrt_nonneg (x - 8)
    have h2 : sqrt (x - 8) - 9 ≠ 0 := by
      by_contra h
      have h3 : sqrt (x - 8) = 9 := by linarith
      rw [h3] at h_eq
      norm_num at h_eq 
    have h3 : sqrt (x - 8) - 4 ≠ 0 := by
      by_contra h 
      have h4 : sqrt (x - 8) = 4 := by linarith 
      rw [h4] at h_eq 
      norm_num at h_eq 
    have h4' : sqrt (x - 8) + 4 ≠ 0 := by
      have h5 : sqrt (x - 8) ≥ 0 := Real.sqrt_nonneg (x - 8)
      have h6 : sqrt (x - 8) + 4 > 0 := by nlinarith
      linarith 
    have h5' : sqrt (x - 8) + 9 ≠ 0 := by
      have h6 : sqrt (x - 8) ≥ 0 := Real.sqrt_nonneg (x - 8)
      have h7 : sqrt (x - 8) + 9 > 0 := by nlinarith
      linarith 
    set y := sqrt (x - 8) with hy 
    have h6 : y ≥ 0 := by linarith [Real.sqrt_nonneg (x - 8)]
    have hy2 : y^2 = x - 8 := by 
      rw [hy] 
      rw [Real.sq_sqrt] 
      linarith
    field_simp [h2, h3, h4', h5'] at h_eq
    have h7 : (y - 3) * (y - 6) = 0 := by 
      nlinarith [sq_nonneg (y^2 - 9), sq_nonneg (y - 3), sq_nonneg (y - 6), sq_nonneg (y * (y - 3)), sq_nonneg (y * (y - 6)), sq_nonneg ((y - 3) * (y - 6)), h6]
    cases' (mul_eq_zero.mp h7) with hy3 hy6 
    · -- y - 3 = 0, so y = 3 
      have h8 : y = 3 := by linarith 
      have h10 : x = 17 := by 
        rw [h8] at hy2 
        nlinarith 
      left 
      linarith 
    · -- y - 6 = 0, so y = 6 
      have h9 : y = 6 := by linarith 
      have h90 : x = 44 := by 
        rw [h9] at hy2 
        nlinarith 
      right 
      linarith
  · -- Assume x = 17 or x = 44, prove the equation
    rintro (h17 | h44)
    · -- x = 17
      rw [h17]
      have h171 : sqrt (17 - 8) = 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h171]
      norm_num 
    · -- x = 44 
      rw [h44]
      have h441 : sqrt (44 - 8) = 6 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h441] 
      norm_num