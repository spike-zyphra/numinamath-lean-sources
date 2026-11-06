import Mathlib

theorem algebra_283337 {A B C : ℝ} (hA : A^2 + B^2 - C^2 ≥ 0) 
    (hNZ1 : A^2 + B^2 ≠ 0) 
    (hNZ2 : A^2 + B*C + B^2 + A*Real.sqrt (A^2 + B^2 - C^2) ≠ 0) :
    (A * C + B * Real.sqrt (A^2 + B^2 - C^2)) / (A^2 + B^2) =
    ((B + C) * (A + Real.sqrt (A^2 + B^2 - C^2))) /
    (A^2 + B * C + B^2 + A * Real.sqrt (A^2 + B^2 - C^2)) := by
  have h1 : 0 ≤ A ^ 2 + B ^ 2 - C ^ 2 := hA
  have h2 : Real.sqrt (A ^ 2 + B ^ 2 - C ^ 2) ^ 2 = A ^ 2 + B ^ 2 - C ^ 2 := by 
    apply Real.sq_sqrt
    linarith
  field_simp [hNZ1, hNZ2]
  nlinarith [hA, sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (B - C), sq_nonneg (A), sq_nonneg (B), sq_nonneg (C), sq_nonneg (A - Real.sqrt (A^2 + B^2 - C^2)), sq_nonneg (B - Real.sqrt (A^2 + B^2 - C^2)), sq_nonneg (C - Real.sqrt (A^2 + B^2 - C^2)), mul_nonneg (show 0 ≤ Real.sqrt (A^2 + B^2 - C^2) by apply Real.sqrt_nonneg) (show 0 ≤ Real.sqrt (A^2 + B^2 - C^2) by apply Real.sqrt_nonneg)]