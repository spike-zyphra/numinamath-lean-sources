import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_273674 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
  (hsum : ∑ i : Fin n, x i = 0) (m M : ℝ)
  (hm : ∃ i : Fin n, x i = m) (hM : ∃ i : Fin n, x i = M)
  (hmin : ∀ i : Fin n, x i ≥ m) (hmax : ∀ i : Fin n, x i ≤ M) :
  ∑ i : Fin n, (x i)^2 ≤ -n * m * M := by
  have h1 : ∀ i : Fin n, (x i - m) * (x i - M) ≤ 0 := by
    intro i
    have h2 : x i ≥ m := hmin i
    have h3 : x i ≤ M := hmax i
    have h4 : (x i - m) ≥ 0 := by linarith
    have h5 : (x i - M) ≤ 0 := by linarith
    nlinarith
  have h2 : ∀ i : Fin n, (x i) ^ 2 ≤ (M + m) * (x i) - m * M := by
    intro i
    have h1' : (x i - m) * (x i - M) ≤ 0 := h1 i
    nlinarith
  have h4 : ∑ i : Fin n, ((x i) ^ 2) ≤ ∑ i : Fin n, ((M + m) * (x i) - m * M) := by
    apply Finset.sum_le_sum
    intro i hi
    specialize h2 i
    linarith
  have h5 : ∑ i : Fin n, ((M + m) * (x i) - m * M) = (M + m) * (∑ i : Fin n, (x i)) - n * m * M := by 
    simp [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, Finset.sum_const, Finset.card_univ]
    <;> ring
  rw [h5] at h4
  rw [hsum] at h4
  nlinarith