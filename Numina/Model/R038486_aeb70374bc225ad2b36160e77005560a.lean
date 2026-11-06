import Mathlib


theorem algebra_19806 (b j : Fin 4 → ℕ)
    (h₀ : ∀ i, b i ∈ Finset.Icc 0 100)
    (h₁ : ∀ i, j i ∈ Finset.Icc 0 100)
    (h₂ : ∑ i, b i = 312)
    (h₃ : j 0 = b 0 + 10 ∧ j 1 = b 1 - 10)
    (h₄ : j 2 = b 2 + 20 ∧ j 3 = b 3 + 20) :
    (∑ i, j i) / 4 - 78 = 10 := by

  rcases h₃ with ⟨h₃₀, h₃₁⟩
  rcases h₄ with  ⟨h₄₀, h₄₁⟩

  have h7 : b 1 ≥ 10 := by
    by_contra h
    push_neg at h
    have h13 : b 1 < 10 := by
      omega
    have h14 : b 0 + b 1 + b 2 + b 3 = 312 := by
      have h15 : ∑ i, b i = 312 := h₂
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h15 ⊢
      omega
    have h17 : b 1 ≤ 9 := by
      omega
    have h18 : b 0 + b 2 + b 3 ≥ 303 := by
      omega
    have h19 : b 0 ≤ 100 := by
      have h9 : b 0 ∈ Finset.Icc (0 : ℕ) 100 := h₀ 0
      simp at h9 ⊢
      omega
    have h20 : b 2 ≤ 100 := by
      have h9 : b 2 ∈ Finset.Icc (0 : ℕ) 100 := h₀ 2
      simp at h9 ⊢
      omega
    have h21 : b 3 ≤ 100 := by
      have h9 : b 3 ∈ Finset.Icc (0 : ℕ) 100 := h₀ 3
      simp at h9 ⊢
      omega
    have h22 : b 0 + b 2 + b 3 ≤ 300 := by
      omega
    omega

  -- Now we can compute $\sum j_i$
  have h5 : ∑ i : Fin 4, j i = 352 := by
    have eq1 : j 0 = b 0 + 10 := by
      omega
    have eq2 : j 1 = b 1 - 10 := by
      omega
    have eq3 : j 2 = b 2 + 20 := by
      omega
    have eq4 : j 3 = b 3 + 20 := by
      omega
    have h14 : b 0 + b 1 + b 2 + b 3 = 312 := by
      have h15 : ∑ i, b i = 312 := h₂
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h15 ⊢
      omega
    have h15 : j 0 + j 1 + j 2 + j 3 = 352 := by
      have eq2' : j 1 = b 1 - 10 := eq2
      have h10 : b 1 ≥ 10 := h7
      omega
    have h17 : ∑ i : Fin 4, j i = j 0 + j 1 + j 2 + j 3 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    omega

  omega