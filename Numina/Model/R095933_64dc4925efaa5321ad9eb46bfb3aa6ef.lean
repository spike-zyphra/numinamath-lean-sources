import Mathlib

theorem number_theory_178045 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) :
    IsSquare (400 * 10000 + n) ↔ n = 4001 ∨ n = 8004 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  constructor
  · -- Assume it's a perfect square, derive n.
    intro h
    rcases h with ⟨r, hr⟩
    have h1 : r ≤ 2004 := by
      by_contra h2
      push_neg at h2
      have h3 : r ^ 2 > 4009999 := by
        have h4 : r >= 2005 := by omega
        have h5 : r ^ 2 >= 2005 ^ 2 := by apply Nat.pow_le_pow_of_le_left h4 2
        have h6 : 2005 ^ 2 > 4009999 := by norm_num
        linarith [h5, h6]
      have h4 : r ^ 2 <= 4009999 := by
        nlinarith
      linarith
    have h2 : r >= 2001 := by
      by_contra h3
      push_neg at h3
      have h4 : r ^ 2 <= 4000000 := by
        have h5 : r <= 2000 := by omega
        have h6 : r ^ 2 <= 2000 ^ 2 := by apply Nat.pow_le_pow_of_le_left h5 2
        norm_num at h6 ⊢
        linarith
      have h5 : r ^ 2 >= 4001000 := by
        nlinarith
      linarith
    interval_cases r <;> omega
  · -- Assume n is 4001 or 8004, prove it's a perfect square
    rintro (h | h)
    · -- n = 4001
      rw [h]
      native_decide
    · -- n = 8004
      rw [h]
      native_decide