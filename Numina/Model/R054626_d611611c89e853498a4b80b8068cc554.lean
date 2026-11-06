import Mathlib

theorem algebra_6331 (a b c : ℕ) (h₀ : a * b * c = 216) (h₁ : b = 2 * a) (h₂ : c = 4 * a) :
    a = 3 := by
  rw [h₁, h₂] at h₀
  -- After substitution we get a * (2a) * (4a) = 216
  -- This simplifies to 8 * a^3 = 216
  -- So a^3 = 27
  have h3 : a * (2 * a) * (4 * a) = 8 * a^3 := by
    ring_nf
  rw [h3] at h₀
  -- Now we have 8 * a^3 = 216, which simplifies to a^3 = 27
  have h4 : a^3 = 27 := by
    nlinarith
  -- Now we need to solve a^3 = 27 for natural number a
  have h5 : a = 3 := by
    have h6 : a ≤ 3 := by
      by_contra h
      push_neg at h
      have h8 : a ≥ 4 := by omega
      have h7 : a^3 > 27 := by
        have h9 : a ^ 3 ≥ 4 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left h8 3
        norm_num at h9 ⊢
        linarith
      linarith [h4, h7]
    have h7 : a ≥ 3 := by
      by_contra h
      push_neg at h
      have h8 : a ≤ 2 := by omega
      have h9 : a^3 ≤ 8 := by
        have h10 : a ≤ 2 := by linarith
        have h11 : a^3 ≤ 2^3 := by
          apply Nat.pow_le_pow_of_le_left h10 3
        norm_num at h11 ⊢
        linarith
      have h4' : a^3 = 27 := h4
      linarith [h4', h9]
    omega
  exact h5