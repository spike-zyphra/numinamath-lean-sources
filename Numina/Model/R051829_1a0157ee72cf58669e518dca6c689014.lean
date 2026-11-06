import Mathlib

theorem algebra_164777 (x : ℝ) :
    (x + 2)^4 + x^4 = 82 ↔ x = -3 ∨ x = 1 := by
  constructor
  · -- Assume left side: $(x + 2)^4 + x^4 = 82$, prove right side: $x = -3 ∨ x = 1$
    intro h
    have h1 : (x + 1) ^ 2 = 4 := by
      nlinarith [sq_nonneg (x + 1 - 2), sq_nonneg (x + 1 + 2), sq_nonneg (x + 1), sq_nonneg (x + 1 - 2 * (x + 1)), sq_nonneg (x + 1 + 2 * (x + 1)), sq_nonneg (x + 1), sq_nonneg ((x + 1) ^ 2 - 4)]
    have h2 : (x + 1) = 2 ∨ (x + 1) = -2 := by
      have h : (x + 1) ^ 2 - 4 = 0 := by linarith
      have h2 : (x + 1 - 2) * (x + 1 + 2) = 0 := by
        ring_nf at h ⊢
        linarith
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- x + 1 - 2 = 0
        left
        linarith
      · -- x + 1 + 2 = 0
        right
        linarith
    cases' h2 with h3 h4
    · -- x + 1 = 2, so x = 1
      right
      linarith
    · -- x + 1 = -2, so x = -3
      left
      linarith
  · -- Assume right side: $x = -3 ∨ x = 1$, prove left side: $(x + 2)^4 + x^4 = 82$
    rintro (h | h)
    · -- If x = -3, check equality
      rw [h]
      norm_num
    · -- If x = 1, check equality
      rw [h]
      norm_num