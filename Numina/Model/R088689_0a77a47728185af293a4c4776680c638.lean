import Mathlib

theorem number_theory_323406 (l w h : ℕ) (h₀ : l > 0) (h₁ : w > 0) (h₂ : h > 0)
    (h₃ : l * w * h = 96) (h₄ : w = 3 * l) (h₅ : h = 4 * l) :
    l = 2 ∧ w = 6 ∧ h = 8 := by
  have hw : w = 3 * l := h₄
  have hh : h = 4 * l := h₅
  rw [hw, hh] at h₃
  have h6 : l ^ 3 = 8 := by
    ring_nf at h₃ ⊢
    nlinarith
  have h3 : l = 2 := by
    have h4 : l ^ 3 = 8 := h6
    have h5 : l = 2 := by
      have h3 : l ≤ 2 := by
        by_contra h
        push_neg at h
        have h3 : l ≥ 3 := by
          omega
        have h4 : l ^ 3 ≥ 27 := by
          have h8 : l ≥ 3 := h3
          have h9 : (3 : ℕ) ^ 3 = 27 := by norm_num
          have h10 : l ^ 3 ≥ (3 : ℕ) ^ 3 := by
            apply Nat.pow_le_pow_of_le_left h8 3
            all_goals linarith
          linarith
        nlinarith
      interval_cases l <;> omega
    exact h5
  have hw2 : w = 6 := by
    rw [show l = 2 by linarith] at hw
    omega
  have hh2 : h = 8 := by
    rw [show l = 2 by linarith] at hh
    omega
  exact ⟨by omega, by omega, by omega⟩