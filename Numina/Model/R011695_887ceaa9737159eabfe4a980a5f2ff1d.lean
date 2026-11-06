import Mathlib

theorem algebra_144975 (y : ℕ → ℕ) (hy : ∀ x, y x = x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 + 2 * x + 1) :
    ¬ (∀ x, IsSquare (y x)) := by
  intro h
  have h1 := h 1
  rw [hy] at h1
  have h2 : IsSquare (1 ^ 4 + 2 * 1 ^ 3 + 2 * 1 ^ 2 + 2 * 1 + 1) := h1
  have h3 : ∃ s, 1 ^ 4 + 2 * 1 ^ 3 + 2 * 1 ^ 2 + 2 * 1 + 1 = s * s := by
    simpa using h2
  rcases h3 with ⟨k, hk⟩
  norm_num at hk
  have h4 : k ≤ 3 := by
    by_contra h4
    push_neg at h4
    have h5 : k ≥ 4 := by 
      omega
    have h6 : k ^ 2 ≥ 16 := by
      have h7 : k ^ 2 ≥ 4 ^ 2 := by
        apply Nat.pow_le_pow_left
        omega
      omega
    have h7 : k ^ 2 = 8 := by
      nlinarith [hk]
    omega
  interval_cases k <;> omega