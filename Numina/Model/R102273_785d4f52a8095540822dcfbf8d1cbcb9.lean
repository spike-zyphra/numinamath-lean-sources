import Mathlib

open Finset Real

theorem inequalities_189986 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (h₁ : ∑ i : Fin n, (a i)^2 = 1) (h₂ : ∑ i : Fin n, (b i)^2 = 1) :
    |∑ i : Fin n, a i * b i| ≤ 1 := by
  have h3 : (∑ i : Fin n, a i * b i) ^ 2 ≤ (∑ i : Fin n, (a i)^2) * (∑ i : Fin n, (b i)^2) := by 
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [h₁, h₂] at h3
  have h4 : (∑ i : Fin n, a i * b i) ^ 2 ≤ 1 := by
    nlinarith
  have h5 : -1 ≤ ∑ i : Fin n, a i * b i := by 
    nlinarith [sq_nonneg (∑ i : Fin n, a i * b i)]
  have h6 : ∑ i : Fin n, a i * b i ≤ 1 := by 
    nlinarith [sq_nonneg (∑ i : Fin n, a i * b i)]
  apply abs_le.mpr
  constructor <;> linarith [h5, h6]