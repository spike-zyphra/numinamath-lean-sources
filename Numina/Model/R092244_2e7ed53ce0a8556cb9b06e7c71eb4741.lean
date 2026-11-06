import Mathlib

theorem number_theory_194928 (n : ℕ) (h₀ : n > 0) (h₁ : 110 ≤ ∑ i ∈ Finset.range n, (i + 1)) (h₂ : ∑ i ∈ Finset.range n, (i + 1) ≤ 130) :
    n = 15 := by 
  have h3 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := by 
    intro n 
    induction n with
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih] 
      ring_nf 
      omega
  have h4 : n * (n + 1) / 2 ≥ 110 := by 
    have h5 : ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := h3 n
    linarith [h₁, h5]
  have h6 : n * (n + 1) / 2 ≤ 130 := by 
    have h7 : ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := h3 n
    linarith [h₂, h7]
  have h8 : n ≤ 15 := by 
    by_contra h 
    push_neg at h 
    have h9 : n * (n + 1) / 2 > 130 := by 
      have h10 : n ≥ 16 := by omega 
      have h11 : n * (n + 1) ≥ 16 * 17 := by nlinarith 
      have h12 : n * (n + 1) / 2 ≥ 136 := by 
        omega 
      omega 
    linarith 
  have h9 : n ≥ 15 := by 
    by_contra h 
    push_neg at h 
    have h10 : n ≤ 14 := by omega 
    interval_cases n <;> norm_num [h3] at h4 <;> omega 
  linarith