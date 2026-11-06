import Mathlib

theorem algebra_227819 (x : ℝ) :
    (1 + x + x^2) * ∑ i ∈ Finset.range 11, x ^ i =
    (∑ i ∈ Finset.range 7, x ^ i) ^ 2 ↔ x = -1 ∨ x = 0 := by
  constructor
  · -- Assume left side, prove right side
    intro h_eq
    simp [Finset.sum_range_succ] at h_eq
    have h_eq2 : x ^ 3 * (x ^ 8 - 2 * x ^ 4 + 1) = 0 := by
      nlinarith [sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x ^ 2), sq_nonneg (x ^ 3), sq_nonneg (x ^ 5)]
    cases' (mul_eq_zero.mp h_eq2) with h1 h2
    · -- Case $x^3 = 0$, so $x = 0$
      right
      have h_eq0 : x ^ 3 = 0 := by
        nlinarith
      have h_eq00 : x = 0 := by
        have : x ^ 3 = 0 := h_eq0
        simp at this ⊢
        <;> nlinarith
      exact h_eq00
    · -- Case $x^8 - 2 * x^4 + 1 = 0$
      have h_eq3 : x ^ 8 - 2 * x ^ 4 + 1 = 0 := by
        nlinarith
      have h_eq4 : (x ^ 4 - 1) ^ 2 = 0 := by
        nlinarith
      have h_eq5 : x ^ 4 - 1 = 0 := by
        apply pow_eq_zero 
        exact h_eq4
      have h_eq6 : x ^ 4 = 1 := by
        linarith
      have h_eq7 : x ^ 2 = 1 ∨ x ^ 2 = -1 := by
        have : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp this) with h_eq8 h_eq9
        · -- Case x^2 -1 = 0, so x^2 =1
          left
          linarith
        · -- Case x^2 +1 =0, so x^2 = -1
          right
          linarith
      cases' h_eq7 with h_eq8 h_eq9
      · -- Case x ^ 2 = 1, so x = 1 ∨ x = -1
        have h_eq9 : x = 1 ∨ x = -1 := by
          have h_eq10 : x ^ 2 = 1 := h_eq8
          rw [sq_eq_one_iff] at h_eq10
          tauto
        cases' h_eq9 with h_eq10 h_eq11
        · -- Case x = 1
          rw [show x = (1 : ℝ) by linarith] at h_eq
          norm_num at h_eq
        · -- Case x = -1
          left
          linarith
      · -- Case x ^ 2 = -1
        nlinarith [sq_nonneg (x)]
  · -- Assume right side, prove left side
    rintro (h | h)
    · -- Case x = -1
      rw [show x = -1 by linarith]
      norm_num [Finset.sum_range_succ]
    · -- Case x = 0
      rw [show x = (0 : ℝ) by linarith]
      norm_num [Finset.sum_range_succ]