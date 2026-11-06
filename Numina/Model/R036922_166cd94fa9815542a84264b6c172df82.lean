import Mathlib

open Real

theorem inequalities_599277 {n : ℕ} (hn : 0 < n) (a x : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) :
    ∑ i, (x i)^2 / a i ≥ (∑ i, x i)^2 := by
  have h3 : ∀ i, 0 < a i := ha
  have h3' : ∑ i : Fin n, (x i) ^ 2 / a i ≥ (∑ i : Fin n, (x i)) ^ 2 / (∑ i : Fin n, a i) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi
    have h3i : 0 < a i := h3 i
    exact h3i
  have h8 : (∑ i : Fin n, a i) = 1 := hsum
  have h3'' : (∑ i : Fin n, (x i)) ^ 2 / (∑ i : Fin n, a i) = (∑ i : Fin n, (x i)) ^ 2 := by
    rw [h8]
    norm_num
  linarith [h3', h3'']