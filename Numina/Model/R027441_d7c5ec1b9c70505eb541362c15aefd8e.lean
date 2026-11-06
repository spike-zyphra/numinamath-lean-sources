import Mathlib

open Finset Real

theorem inequalities_250217 {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ)
    (hy : ∀ i, 0 < y i) :
    (∑ i, y i) * (∑ i, (x i)^2 / y i) ≥ (∑ i, x i)^2 := by
  have h2 : ∀ i, y i > 0 := by
    intro i
    exact hy i
  have h3 : (∑ i : Fin n, x i) ^ 2 ≤ (∑ i : Fin n, y i) * (∑ i : Fin n, (x i) ^ 2 / y i) := by
    have h4 : (∑ i : Fin n, x i) ^ 2 = (∑ i : Fin n, (Real.sqrt (y i) * (x i / Real.sqrt (y i))) ) ^ 2 := by
      congr
      funext i
      have h5 : 0 < y i := h2 i
      have h6 : Real.sqrt (y i) > 0 := by apply Real.sqrt_pos.mpr h5
      field_simp [h6]
      <;> nlinarith [Real.sqrt_nonneg (y i)]
    rw [h4]
    have h7 : (∑ i : Fin n, (Real.sqrt (y i) * (x i / Real.sqrt (y i))) ) ^ 2 ≤
      (∑ i : Fin n, (Real.sqrt (y i) ) ^ 2) * (∑ i : Fin n, (x i / Real.sqrt (y i)) ^ 2) := by
      apply Finset.sum_mul_sq_le_sq_mul_sq
    have h8 : (∑ i : Fin n, (Real.sqrt (y i) ) ^ 2) = (∑ i : Fin n, y i) := by
      congr
      funext i
      have h5 : 0 < y i := h2 i
      have h6 : Real.sqrt (y i) > 0 := by apply Real.sqrt_pos.mpr h5
      have h7 : (Real.sqrt (y i) ) ^ 2 = y i := Real.sq_sqrt (by linarith)
      simpa using h7
    have h9 : (∑ i : Fin n, (x i / Real.sqrt (y i)) ^ 2) = (∑ i : Fin n, (x i) ^ 2 / y i) := by
      congr
      funext i
      have h5 : 0 < y i := h2 i
      have h6 : Real.sqrt (y i) > 0 := by apply Real.sqrt_pos.mpr h5
      have h7 : (x i / Real.sqrt (y i)) ^ 2 = (x i) ^ 2 / y i := by
        field_simp
        <;> nlinarith [Real.sqrt_nonneg (y i)]
      simpa using h7
    rw [h8, h9] at h7
    linarith
  linarith [h3]