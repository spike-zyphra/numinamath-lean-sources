import Mathlib

theorem algebra_21950 (N : ℕ) (h : N > 0) :
    ∑ i ∈ Finset.range N, (2 * i + 1) = 121 ↔ N = 11 := by
  constructor
  · -- Assume the sum is 121, prove N = 11
    intro h1
    have h2 : ∀ N : ℕ, ∑ i in Finset.range N, (2 * i + 1 : ℕ) = N ^ 2 := by
      intro N
      induction N with
      | zero =>
        simp
      | succ N ihN =>
        rw [Finset.sum_range_succ, ihN]
        ring_nf
        <;> omega
    have h3 : N ^ 2 = 121 := by
      have h4 : ∑ i in Finset.range N, (2 * i + 1 : ℕ) = N ^ 2 := h2 N
      linarith [h1, h4]
    have h4 : N ≤ 11 := by
      by_contra h5
      push_neg at h5
      have h6 : N ≥ 12 := by linarith
      have h7 : N ^ 2 ≥ 144 := by nlinarith
      nlinarith [h3]
    have h5 : N ≥ 11 := by
      by_contra h6
      push_neg at h6
      have h7 : N ≤ 10 := by linarith
      have h8 : N ^ 2 ≤ 100 := by nlinarith
      nlinarith [h3]
    have hN : N = 11 := by linarith 
    exact hN
  · -- Assume N = 11, prove the sum is 121
    intro hN
    rw [hN]
    native_decide