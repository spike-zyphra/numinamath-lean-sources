import Mathlib

open Real

theorem algebra_130321 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (h₁ : ∑ i : Fin n, (a i)^2 = 4) (h₂ : ∑ i : Fin n, (b i)^2 = 9) :
    ∑ i : Fin n, a i * b i ≤ 6 := by
  have h3 : (∑ i : Fin n, a i * b i) ^ 2 ≤ (∑ i : Fin n, (a i)^2) * (∑ i : Fin n, (b i)^2) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [h₁, h₂] at h3
  have h4 : (∑ i : Fin n, a i * b i) ^ 2 ≤ 36 := by
    nlinarith
  have h5 : (∑ i : Fin n, a i * b i) ≤ 6 := by
    nlinarith [sq_nonneg (∑ i : Fin n, a i * b i - 6), sq_nonneg (∑ i : Fin n, a i * b i + 6)]
  exact h5