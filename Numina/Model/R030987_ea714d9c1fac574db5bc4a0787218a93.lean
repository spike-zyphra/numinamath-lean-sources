import Mathlib

theorem algebra_171142 (x : ℝ) (hx : x ≠ 2) :
    (x^3 - 2 * x^2 - 5 * x + 6) / (x - 2) > 0 ↔ x < -2 ∨ x ∈ Set.Ioo 1 2 ∨ x > 3 := by
  have h1 : (x^3 - 2 * x^2 - 5 * x + 6) = (x + 2) * (x - 1) * (x - 3) := by
    ring
  have h2 : (x^3 - 2 * x^2 - 5 * x + 6) / (x - 2) > 0 ↔ ((x^3 - 2 * x^2 - 5 * x + 6) > 0 ∧ x - 2 > 0) ∨ ((x^3 - 2 * x^2 - 5 * x + 6) < 0 ∧ x - 2 < 0) := by
    apply Iff.intro
    · -- Assume (x^3 - 2 * x^2 - 5 * x + 6) / (x - 2) > 0, prove the disjunction
      intro h
      apply div_pos_iff.mp at h
      exact h
    · -- Assume the disjunction, prove (x^3 - 2 * x^2 - 5 * x + 6) / (x - 2) > 0
      intro h
      apply div_pos_iff.mpr
      exact h
  rw [h2, h1]
  constructor
  · -- Assume $\frac{(x + 2)(x - 1)(x - 3)}{x - 2} > 0$ prove $x \in (-\infty, -2) \cup (1, 2) \cup (3, \infty)$
    intro h
    cases h with
    | inl h_pos1 =>
      have numer_pos : (x + 2) * (x - 1) * (x - 3) > 0 := by
        nlinarith
      have den_pos : x - 2 > 0 := by
        nlinarith
      have h3 : x > 3 := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 1), sq_nonneg (x - 3)]
      right
      right
      exact h3
    | inr h_neg =>
      have numer_neg : (x + 2) * (x - 1) * (x - 3) < 0 := by
        nlinarith
      have den_neg : x - 2 < 0 := by
        nlinarith
      have h4 : x < 2 := by linarith
      by_cases h5 : x < -2
      · -- Prove relationship for interval
        left
        exact h5
      · -- Now we have to move from h
        have h1 : x ≥ -2 := by nlinarith
        have h4 : x < 2 := by linarith
        have h8 : x ∈ Set.Ioo 1 2 := by
          constructor <;> nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x - 3)]
        right
        left
        exact h8
  · -- Assume $x \in (-\infty, -2) \cup (1, 2) \cup (3, \infty)$ prove $\frac{(x + 2)(x - 1)(x - 3)}{x - 2} > 0$
    intro h
    rcases h with h1 | h2 | h3
    · -- Case $x < -2$
      have h4 : x - 2 < 0 := by linarith
      have h6 : (x + 2) * (x - 1) * (x - 3) < 0 := by
        nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x - 3)]
      apply Or.inr
      constructor
      · -- Numerator negative
        nlinarith
      · -- Denominator negative
        nlinarith
    · -- Case $x \in (1, 2)$
      rcases h2 with ⟨hx1, hx2⟩
      have h4 : x - 2 < 0 := by linarith
      have h6 : (x + 2) * (x - 1) * (x - 3) < 0 := by
        nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x - 3)]
      apply Or.inr
      constructor
      · -- Numerator negative
        nlinarith
      · -- Denominator negative
        nlinarith
    · -- Case $x > 3$
      have h4 : x - 2 > 0 := by linarith
      have h6 : (x + 2) * (x - 1) * (x - 3) > 0 := by
        have h21 : x + 2 > 0 := by linarith
        have h211 : x - 1 > 0 := by linarith
        have h2111 : x - 3 > 0 := by linarith
        positivity
      apply Or.inl
      constructor
      · -- Numerator positive
        nlinarith
      · -- Denominator positive
        nlinarith