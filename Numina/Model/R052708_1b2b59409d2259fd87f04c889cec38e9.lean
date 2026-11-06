import Mathlib

theorem number_theory_4195
    (n : ℕ)
    (h₀ : n ∈ Finset.Icc 1000 9999)
    (h₁ : ∃ k, n = k^2)
    (h₂ : (n / 100) % 100 = 2 * (n % 100) + 1) :
    n = 5929 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  rcases h₁ with ⟨k, hk⟩
  have h5 : k ≥ 32 := by
    by_contra h
    push_neg at h
    have : k ^ 2 < 1000 := by
      have h6 : k ≤ 31 := by omega
      have h7 : k ^ 2 ≤ 31 ^ 2 := by
        apply Nat.pow_le_pow_of_le_left h6 2
      norm_num at h7 ⊢
      linarith
    have h8 : n < 1000 := by linarith [hk, this]
    linarith

  have h6 : k ≤ 99 := by
    by_contra h
    push_neg at h
    have : k ^ 2 > 9999 := by
      have h7 : k ≥ 100 := by omega
      have h8 : k ^ 2 ≥ 100 ^ 2 := by
        apply Nat.pow_le_pow_of_le_left h7 2
      norm_num at h8 ⊢
      linarith
    have h9 : n > 9999 := by linarith [hk, this]
    linarith

  interval_cases k <;> norm_num [hk] at h₂ ⊢ <;> omega