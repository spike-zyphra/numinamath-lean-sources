import Mathlib
open Real Finset

theorem inequalities_224550 (a b : ℕ → ℝ) : (∑ i < k, a i * b i) ^ 2 ≤ (∑ i < k, (a i) ^ 2) * (∑ i < k, (b i) ^ 2) := by
  apply Finset.sum_mul_sq_le_sq_mul_sq