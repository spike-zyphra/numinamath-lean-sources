import Mathlib

theorem algebra_205423 {x : ℝ} (hx : x ≠ 1) :
    (x^7 - 1) / (x^5 - 1) = (x^5 - 1) / (x^3 - 1) ↔ x = 0 ∨ x = -1 := by 
  constructor
  · -- Assume equality of fractions, prove x = 0 ∨ x = -1
    intro h
    have h1 : x^5 - 1 ≠ 0 := by
      by_contra h1
      have : x^5 = 1 := by linarith 
      have h2 : x = 1 := by
        have h2 : x^5 - 1 = 0 := by linarith 
        have h3 : x^5 - 1 = (x - 1) * (x^4 + x^3 + x^2 + x + 1) := by ring
        rw [h3] at h2
        cases' (mul_eq_zero.mp h2) with h4 h5
        · -- x - 1 = 0 
          linarith 
        · -- x^4 + x^3 + x^2 + x + 1 = 0 
          have h6 : x^4 + x^3 + x^2 + x + 1 > 0 := by
            nlinarith [sq_nonneg (x^2 - x), sq_nonneg (x^2 + x), sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
          nlinarith 
      contradiction 
    have h2 : x^3 - 1 ≠ 0 := by
      by_contra h1
      have : x^3 = 1 := by linarith 
      have h2 : x = 1 := by
        have h4 : x^3 - 1 = 0 := by linarith 
        have h5 : x^3 - 1 = (x - 1) * (x^2 + x + 1) := by ring
        rw [h5] at h4
        cases' (mul_eq_zero.mp h4) with h8 h9
        · -- x - 1 = 0 
          linarith 
        · -- x^2 + x + 1 = 0 
          have h10 : x^2 + x + 1 > 0 := by nlinarith [sq_nonneg (x + 1/2)]
          nlinarith 
      contradiction 
    have h3 : (x^7 - 1) * (x^3 - 1) = (x^5 - 1)^2 := by
      field_simp [h1, h2] at h ⊢
      nlinarith 
    have h4 : x^7 - 2 * x^5 + x^3 = 0 := by
      nlinarith 
    have h5 : x^3 * (x^2 - 1)^2 = 0 := by
      nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x^2 - 2), sq_nonneg (x^3 - x^5)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case x^3 = 0 
      have h8 : x^3 = 0 := h6
      -- Now prove x = 0 
      have h9 : x = 0 := by
        have h10 : x^3 = 0 := h8
        have h11 : x^3 = 0 := h10
        have h12 : x = 0 := by
          have h13 : x^3 = 0 := h11
          simp at h13 
          nlinarith [sq_nonneg x, sq_nonneg (x^2)]
          <;> tauto 
          <;> norm_num at h13 
        exact h12 
      left 
      exact h9 
    · -- Case (x^2 - 1)^2 = 0 
      have h8 : x^2 - 1 = 0 := by 
        nlinarith [sq_nonneg (x^2 - 1)]
      have h9 : (x - 1) * (x + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h9) with h10 h11 
      · -- Case x - 1 = 0 
        exfalso 
        apply hx 
        linarith 
      · -- Case x + 1 = 0 
        have h12 : x = -1 := by 
          linarith 
        right 
        exact h12 
  · -- Assume x = 0 ∨ x = -1, prove equality 
    rintro (h | h)
    · -- Case x = 0 
      rw [h]
      norm_num 
    · -- Case x = -1 
      rw [h]
      norm_num