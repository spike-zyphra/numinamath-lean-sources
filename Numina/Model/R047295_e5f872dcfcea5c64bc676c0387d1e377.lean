import Mathlib

theorem number_theory_163789 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : ∃ k, n * 6 = k ^ 3)
    (h₂ : ∃ m, n / 6 = m ^ 2) : n = 7776 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨m, hm⟩
  have h3 : n ≥ 1000 := h₀.1
  have h4 : n ≤ 9999 := h₀.2
  have h5 : k ^ 3 = n * 6 := by linarith
  have h6 : k ≤ 39 := by
    by_contra h
    push_neg at h
    have h7 : k ^ 3 > 59994 := by
      have h8 : k ≥ 40 := by omega
      have h9 : k ^ 3 ≥ 64000 := by
        have h10 : k ≥ 40 := h8
        have h11 : k ^ 3 ≥ 40 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left h10 3
        norm_num at h11 ⊢
        linarith
      linarith
    have h7 : n * 6 > 59994 := by linarith [h5, h7]
    have h8 : n > 9999 := by
      omega
    omega
  have h7 : k ≥ 18 := by
    by_contra h
    push_neg at h
    have h8 : k < 18 := by omega
    have h9 : k ^ 3 < 6000 := by
      have h10 : k < 18 := h8
      have h11 : k ≤ 17 := by omega
      have h12 : k ^ 3 ≤ 17 ^ 3 := by
        have h13 : k ≤ 17 := h11
        have h14 : k ^ 3 ≤ 17 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left h13 3
        linarith
      norm_num at h12 ⊢
      linarith
    have h10 : n * 6 < 6000 := by linarith [h5, h9]
    have h11 : n < 1000 := by
      omega
    omega
  have h9 : m ≤ 40 := by
    have h11 : m ^ 2 ≤ 1666 := by
      have h12 : n ≤ 9999 := h4
      have h13 : n / 6 ≤ 1666 := by
        omega
      have h14 : m ^ 2 = n / 6 := by
        omega
      omega
    have h17 : m ≤ 40 := by
      nlinarith
    exact h17
  interval_cases k <;> try { 
    omega
  } <;> try { 
    interval_cases m <;> omega
  }