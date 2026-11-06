import Mathlib

open Real

theorem inequalities_258006 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    (∑ i, a i * b i) ≤ (∑ i, a i ^ 2) ^ ((1 : ℝ) / 2) * (∑ i, b i ^ 2) ^ ((1 : ℝ) / 2) := by
  have h1 : (∑ i : Fin n, a i * b i) ^ 2 ≤ (∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h2 : (∑ i : Fin n, a i * b i) ≤ Real.sqrt ((∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2)) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have h3 : Real.sqrt ((∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2)) = Real.sqrt (∑ i : Fin n, (a i) ^ 2) * Real.sqrt (∑ i : Fin n, (b i) ^ 2) := by 
    rw [Real.sqrt_mul (by positivity)]
  have h4 : (∑ i : Fin n, (a i) ^ 2) ^ ((1 : ℝ) / 2) = Real.sqrt (∑ i : Fin n, (a i) ^ 2) := by 
    rw [← Real.sqrt_eq_rpow]
  have h5 : (∑ i : Fin n, (b i) ^ 2) ^ ((1 : ℝ) / 2) = Real.sqrt (∑ i : Fin n, (b i) ^ 2) := by 
    rw [← Real.sqrt_eq_rpow]
  rw [h4, h5]
  linarith [h2, h3]