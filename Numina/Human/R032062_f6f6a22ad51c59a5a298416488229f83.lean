import Mathlib
/-Solve the following equation for real x:
(x^2 + x - 2)^3 + (2 * x^2 - x - 1)^3 = 27 * (x^2 - 1)^3-/
theorem algebra_122581 (x : ℝ) :
    (x^2 + x - 2)^3 + (2 * x^2 - x - 1)^3 = 27 * (x^2 - 1)^3 ↔
    x = 1 ∨ x = -1 ∨ x = -2 ∨ x = -1 / 2 := by
  constructor
  · -- Forward direction: assume the equation holds, prove x must be one of the given values --
    intro h
    have h1 : (x - 1) * (x + 2) = x^2 + x - 2 := by ring
    have h2 : (2 * x + 1) * (x - 1) = 2 * x^2 - x - 1 := by ring
    have h3 : (x + 1) * (x - 1) = x^2 - 1 := by ring
    rw [←h1, ←h2, ←h3] at h -- we pull the factor x - 1 out of the equation --
    by_cases h4 : x = 1
    · -- Case 1: x = 1
      left
      exact h4
    · -- Case 2: x ≠ 1
      have h5 : x - 1 ≠ 0 := by -- show that x - 1 is not zero, so we can divide by it --
        intro h6
        apply h4
        linarith
      have h_eq : (x + 2) ^ 3 + (2 * x + 1) ^ 3 - 27 * (x + 1) ^ 3 = 0 := by
        have h6 : (x - 1) ^ 3 * ((x + 2) ^ 3 + (2 * x + 1) ^ 3 - 27 * (x + 1) ^ 3) = 0 := by
          ring_nf at h ⊢
          linarith
        have h7 : (x + 2) ^ 3 + (2 * x + 1) ^ 3 - 27 * (x + 1) ^ 3 = 0 := by -- pull the factor (x - 1) ^ 3 out of the equation --
          apply (mul_eq_zero.mp h6).resolve_left
          exact pow_ne_zero 3 h5
        linarith
      have h6 : 2 * x ^ 3 + 7 * x ^ 2 + 7 * x + 2 = 0 := by -- simplify the equation in h_eq --
        ring_nf at h_eq
        linarith
      have h7 : (x + 1) * (2 * x + 1) * (x + 2) = 0 := by -- factor the equation --
        ring_nf at h6 ⊢
        linarith
      cases' (mul_eq_zero.mp h7) with h8 h9  -- now we have three cases, check each of them --
      · cases' (mul_eq_zero.mp h8) with h10 h11
        · -- x + 1 = 0 → x = -1
          right
          left
          linarith
        · -- 2x + 1 = 0 → x = -1/2
          right
          right
          right
          linarith
      · -- x + 2 = 0 → x = -2
        right
        right
        left
        linarith
 
  · -- Backward direction: prove that each of the given values satisfies the equation
    rintro (h | h | h | h)
    · -- x = 1
      rw [h]
      norm_num
    · -- x = -1
      rw [h]
      norm_num
    · -- x = -2
      rw [h]
      norm_num
    · -- x = -1/2
      rw [h]
      norm_num