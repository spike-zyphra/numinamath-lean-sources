import Mathlib

theorem number_theory_245480 (a b : ℕ) :
    2^a * 3^b - 3^(b + 1) + 2^a = 13 ↔ (a, b) = (2, 2) ∨ (a, b) = (3, 0) := by
  constructor
  · -- Forward direction: If the equation holds, then (a, b) is either (2, 2) or (3, 0).
    intro h_eq
    have h1 : a ≤ 5 := by
      by_contra h1
      push_neg at h1
      have h₁ : 2^a ≥ 64 := by
        have h₃ : a ≥ 6 := by omega
        have h₄ : 2 ^ a ≥ 2 ^ 6 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h₃
        have h₅ : 2 ^ 6 = 64 := by norm_num
        linarith
      have h2 : 2^a * 3^b + 2^a - 3^(b + 1) > 13 := by
        by_cases h₃ : b = 0
        · -- Case b = 0
          rw [h₃] at h_eq ⊢
          nlinarith
        · -- Case b > 0
          have h₄ : b > 0 := by omega
          have h₅ : 3 ^ b ≥ 3 := by
            have h₆ : b ≥ 1 := by omega
            have h₇ : 3 ^ 1 = 3 := by norm_num
            have h₈ : 3 ^ b ≥ 3 ^ 1 := by
              apply Nat.pow_le_pow_of_le_right (by norm_num) h₆
            linarith [h₇, h₈]
          nlinarith [sq_nonneg (2 ^ a - 2 ^ 2), sq_nonneg (3 ^ b - 3), sq_nonneg (2 ^ a - 8)]
      omega
    have h2 : b ≤ 4 := by
      by_contra h2
      push_neg at h2
      have h₁ : 3^b ≥ 243 := by
        have h3 : b ≥ 5 := by omega
        have h4 : 3 ^ b ≥ 3 ^ 5 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h3
        have h5 : 3 ^ 5 = 243 := by norm_num
        linarith
      have h6 : a ≤ 5 := h1
      interval_cases a <;> omega
    -- Now we have bounds for a and b, so we can check all possible values
    interval_cases b <;> interval_cases a <;> norm_num at h_eq <;> norm_num
    <;> simp [Prod.ext_iff] at *
    <;> tauto
  · -- Backward direction: If (a, b) is either (2, 2) or (3, 0), then the equation holds.
    rintro (h | h)
    · -- Case (2, 2)
      simp [Prod.mk.injEq] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Case (3, 0)
      simp [Prod.mk.injEq] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num