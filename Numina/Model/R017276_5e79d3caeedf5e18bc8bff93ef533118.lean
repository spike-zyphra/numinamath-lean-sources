import Mathlib

theorem algebra_195695 (x : ℝ) (hx : 2*x^5 - x^4 - 2*x^3 + x^2 - 4*x + 2 = 0) :
    x = Real.sqrt 2 ∨ x = -Real.sqrt 2 ∨ x = 1/2 := by
  have h1 : 2*x^5 - x^4 - 2*x^3 + x^2 - 4*x + 2 = 2 * (x - 1 / 2) * (x^2 - 2) * (x ^ 2 + 1) := by
    ring_nf
  rw [h1] at hx
  cases' (mul_eq_zero.mp hx) with h2 h3
  · cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case where $2\cdot (x - \frac{1}{2}) = 0$, so $x = \frac{1}{2}$
      have h6 : x = 1 / 2 := by
        nlinarith
      right
      right
      exact h6
    · -- Case where $x^2 - 2 = 0$, so $x = \pm \sqrt{2}$
      have h7 : x^2 - 2 = 0 := by
        nlinarith
      have h8 : x^2 = 2 := by
        linarith
      have h9 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
        have h10 : x^2 = 2 := h8
        have h11 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
          apply eq_or_eq_neg_of_sq_eq_sq
          norm_num
          linarith
        exact h11
      cases h9 with
      | inl h10 =>
        left
        exact h10
      | inr h11 =>
        right
        left
        exact h11
  · -- Case where $x^2 + 1 = 0$, which is a contradiction for real $x$.
    have h10 : x ^ 2 + 1 = 0 := by
      nlinarith
    nlinarith [sq_nonneg x]