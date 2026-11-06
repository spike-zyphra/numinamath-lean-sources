import Mathlib

theorem algebra_15791 (x : ℚ) :
    4 * x ^ 4 - 3 * x ^ 3 - 13 * x ^ 2 + 5 * x + 2 = 0 ↔ x = 2 ∨ x = -1 / 4 := by
  constructor
  · -- Assume 4 * x ^ 4 - 3 * x ^ 3 - 13 * x ^ 2 + 5 * x + 2 = 0, prove x = 2 ∨ x = -1 / 4
    intro h
    have h1 : 4 * x ^ 4 - 3 * x ^ 3 - 13 * x ^ 2 + 5 * x + 2 = (x - 2) * (4 * x + 1) * (x^2 + x - 1) := by
      ring
    rw [h1] at h
    cases' (mul_eq_zero.mp h) with h2 h3
    · cases' (mul_eq_zero.mp h2) with h4 h5
      · -- h4 : x - 2 = 0.
        left
        linarith
      · -- h5 : 4 * x + 1 = 0.
        right
        linarith
    · -- h3 : x^2 + x - 1 = 0.
      exfalso
      have h6 : x ^ 2 + x - 1 = 0 := by
        linarith
      have h9 : (2 * x + 1) ^ 2 = 5 := by
        have h10 : 4 * x ^ 2 + 4 * x - 4 = 0 := by
          have h11 : x ^ 2 + x - 1 = 0 := h6
          linarith
        have h12 : (2 * x + 1) ^ 2 = 4 * x ^ 2 + 4 * x + 1 := by
          ring
        linarith [h12, h10]
      have h10 : ¬IsSquare ((5 : ℚ)) := by
        native_decide
      have h14 : IsSquare ((5 : ℚ)) := by
        use (2 * x + 1)
        linarith
      contradiction
  · -- Assume x = 2 ∨ x = -1 / 4, prove 4 * x ^ 4 - 3 * x ^ 3 - 13 * x ^ 2 + 5 * x + 2 = 0
    rintro (h | h)
    · -- x = 2
      rw [h]
      norm_num
    · -- x = -1/4
      rw [h]
      norm_num