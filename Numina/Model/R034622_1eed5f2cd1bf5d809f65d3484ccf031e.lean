import Mathlib

open Real

theorem inequalities_166972 (n : ℕ) (x y : Fin n → ℝ)
    (hy : ∀ i, 0 < y i) :
    (∑ i, y i) * (∑ i, (x i)^2 / y i) ≥ (∑ i, x i)^2 := by
  have h1 : (∑ i : Fin n, x i)^2 = (∑ i : Fin n, ((x i) / Real.sqrt (y i)) * Real.sqrt (y i))^2 := by 
    have h2 : ∀ i : Fin n, ((x i) / Real.sqrt (y i)) * Real.sqrt (y i) = x i := by
      intro i
      have h3 : 0 < y i := hy i
      have h4 : Real.sqrt (y i) > 0 := by positivity
      field_simp
    have h5 : (∑ i : Fin n, ((x i) / Real.sqrt (y i)) * Real.sqrt (y i)) = (∑ i : Fin n, x i) := by 
      apply Finset.sum_congr 
      · rfl 
      · intro i hi 
        specialize h2 i 
        linarith 
    rw [h5] 
  have h2 : (∑ i : Fin n, ((x i) / Real.sqrt (y i)) * Real.sqrt (y i)) ^ 2 ≤ (∑ i : Fin n, ((x i) / Real.sqrt (y i)) ^ 2) * (∑ i : Fin n, (Real.sqrt (y i)) ^ 2) := by
    have h2 : (∑ i : Fin n, ((x i) / Real.sqrt (y i)) * (Real.sqrt (y i))) ^ 2 ≤ (∑ i : Fin n, (( (x i) / Real.sqrt (y i) ) ) ^ 2) * (∑ i : Fin n, (Real.sqrt (y i)) ^ 2) := by
      apply Finset.sum_mul_sq_le_sq_mul_sq 
    simpa using h2
  have h3 : (∑ i : Fin n, ((x i) / Real.sqrt (y i)) ^ 2) = (∑ i : Fin n, (x i)^2 / (y i)) := by
    apply Finset.sum_congr 
    · rfl
    · intro i hi 
      have h3 : 0 < y i := hy i
      have h4 : Real.sqrt (y i) > 0 := by positivity
      have h5 : ((x i) / Real.sqrt (y i)) ^ 2 = (x i)^2 / (y i) := by
        have h6 : Real.sqrt (y i) > 0 := h4
        have h7 : (y i) > 0 := by linarith [h3]
        have h8 : ((x i) / Real.sqrt (y i)) ^ 2 = (x i) ^ 2 / (Real.sqrt (y i) ^ 2) := by
          field_simp
        rw [h8] 
        have h9 : Real.sqrt (y i) ^ 2 = y i := Real.sq_sqrt (by linarith)
        rw [h9] 
      linarith 
  have h4 : (∑ i : Fin n, (Real.sqrt (y i)) ^ 2) = (∑ i : Fin n, y i) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      have h3 : 0 < y i := hy i
      have h4 : Real.sqrt (y i) ^ 2 = y i := Real.sq_sqrt (by linarith)
      linarith 
  rw [h3, h4] at h2 
  linarith [h1, h2]