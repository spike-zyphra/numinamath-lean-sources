import Mathlib

theorem algebra_180112 (x : ℝ) :
    x^6 - 9 * x^3 + 8 > 0 ↔ x < 1 ∨ x > 2 := by
  have h : x^6 - 9 * x^3 + 8 = (x^3 - 1) * (x^3 - 8) := by
    ring
  rw [h]
  constructor
  · -- Assume (x^3 - 1) * (x^3 - 8) > 0, need to prove x < 1 ∨ x > 2
    intro h1
    have h2 : (x^3 - 1) * (x^3 - 8) > 0 := h1
    cases mul_pos_iff.mp h2 with
    | inl h3 =>
      -- Case where both factors are positive
      -- $x^3 - 1 > 0$ and $x^3 - 8 > 0$, which implies $x^3 > 8$, so $x > 2$.
      have h3' : x^3 > 8 := by linarith
      have h4 : x > 2 := by
        nlinarith [sq_nonneg (x^2), sq_nonneg (x - 2), sq_nonneg (x + 2)]
      right
      exact h4
    | inr h3 =>
      -- Case where both factors are negative
      -- $x^3 - 1 < 0$ and $x^3 - 8 < 0$, which implies $x^3 < 1$, so $x < 1$.
      have h1' : x^3 < 1 := by linarith
      have h2' : x < 1 := by
        nlinarith [sq_nonneg (x^2), sq_nonneg (x - 1), sq_nonneg (x + 1)]
      left
      exact h2'
  · -- Assume x < 1 ∨ x > 2, need to prove (x^3 - 1) * (x^3 - 8) > 0
    rintro (h | h)
    · -- Case x < 1
      have h1 : x < 1 := h
      have h1' : x^3 < 1 := by
        nlinarith [sq_nonneg (x^2), sq_nonneg (x - 1), sq_nonneg (x + 1)]
      have h1'' : x^3 - 1 < 0 := by linarith
      have h1''' : x^3 - 8 < 0 := by linarith
      have h2 : (x^3 - 1) * (x^3 - 8) > 0 := by
        apply mul_pos_of_neg_of_neg
        <;> linarith
      exact h2
    · -- Case x > 2
      have h2 : x > 2 := h
      have h2' : x^3 > 8 := by
        nlinarith [sq_nonneg (x^2), sq_nonneg (x - 2), sq_nonneg (x + 2)]
      have h2'' : x^3 - 1 > 0 := by linarith
      have h2''' : x^3 - 8 > 0 := by linarith
      have h3 : (x^3 - 1) * (x^3 - 8) > 0 := by
        apply mul_pos
        all_goals linarith
      exact h3