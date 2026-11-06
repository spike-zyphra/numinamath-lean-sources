import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_118737 {n : ℕ} (hn : 0 < n) (a x : Fin n → ℝ)
  (ha : ∑ i : Fin n, (a i)^2 = 1) (hx : ∑ i : Fin n, (x i)^2 = 1) :
  ∑ i : Fin n, a i * x i ≤ 1 := by
  have h : (∑ i : Fin n, a i * x i)^2 ≤ (∑ i : Fin n, (a i)^2) * (∑ i : Fin n, (x i)^2) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [ha, hx] at h
  have h2 : (∑ i : Fin n, a i * x i) ≤ 1 := by
    nlinarith [sq_nonneg (∑ i : Fin n, a i * x i - 1), sq_nonneg (∑ i : Fin n, a i * x i + 1)]
  exact h2