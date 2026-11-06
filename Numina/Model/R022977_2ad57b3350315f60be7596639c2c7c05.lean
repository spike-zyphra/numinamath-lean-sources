import Mathlib

open Finset Real

theorem inequalities_311604 {n : ℕ} (hn : 0 < n) (a b : ℕ → ℝ)
    (ha : MonotoneOn a (Icc 1 n)) (hb : MonotoneOn b (Icc 1 n))
    (hsum : ∑ i ∈ Icc 1 n, a i = ∑ i ∈ Icc 1 n, b i)
    (hdiff : ∀ i ∈ Icc 1 n, a i ≥ b i ∧ b i ≥ b (i - 1))
    (hij : ∀ i j, i < j ∧ j ≤ n → a j - a i ≥ b j - b i) :
    ∏ i ∈ Icc 1 n, a i ≤ ∏ i ∈ Icc 1 n, b i := by
  have h1 : ∀ i ∈ Icc 1 n, a i ≥ b i := by
    intro i hi
    exact (hdiff i hi).1
  have h2 : ∀ i ∈ Icc 1 n, a i = b i := by
    have h3 : ∑ i ∈ Icc 1 n, a i = ∑ i ∈ Icc 1 n, b i := hsum
    have h4 : ∀ i ∈ Icc 1 n, a i ≥ b i := h1
    have h5 : ∑ i ∈ Icc 1 n, (a i - b i) = 0 := by
      have h5 : ∑ i ∈ Icc 1 n, (a i - b i) = ∑ i ∈ Icc 1 n, a i - ∑ i ∈ Icc 1 n, b i := by
        rw [Finset.sum_sub_distrib]
      rw [h5]
      linarith [h3]
    have h7 : ∀ i ∈ Icc 1 n, (a i - b i) ≥ 0 := by
      intro i hi
      have h10 : a i ≥ b i := h1 i hi
      linarith
    have h6 : ∀ i ∈ Icc 1 n, (a i - b i) = 0 := by
      apply Finset.sum_eq_zero_iff_of_nonneg (fun i hi => by
        have h14 : (a i - b i) ≥ 0 := h7 i hi
        exact h14
      ) |>.mp at h5
      simpa using h5
    intro i hi
    have h13 : (a i - b i) = 0 := h6 i hi
    linarith
  have h3 : ∏ i ∈ Icc 1 n, a i = ∏ i ∈ Icc 1 n, b i := by
    have h4 : ∀ i ∈ Icc 1 n, a i = b i := h2
    apply Finset.prod_congr (by rfl) (fun i hi => h4 i hi)
  linarith [h3]