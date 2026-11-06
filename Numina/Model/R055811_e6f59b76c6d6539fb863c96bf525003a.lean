import Mathlib

theorem algebra_202275 {Q : ℝ} (hQ : Q > 0) (hQ1 : abs (3 * Q - abs (1 - 2 * Q)) = 2) :
    Q = 1 := by
  by_cases h : 1 - 2 * Q ≥ 0
  · -- Case where 1 - 2 * Q ≥ 0, so Q ≤ 1/2
    have h1 : abs (1 - 2 * Q) = 1 - 2 * Q := by
      rw [abs_of_nonneg h]
    rw [h1] at hQ1
    cases eq_or_eq_neg_of_abs_eq hQ1 with
    | inl h2 =>
      -- Simplify: 3 * Q - (1 - 2 * Q) = 2 
      -- This simplifies to 5 * Q = 3, so Q = 3/5 > 1/2, contradicts Q ≤ 1/2
      linarith
    | inr h2 =>
      -- Simplify: 3 * Q - (1 - 2 * Q) = -2 
      -- This simplifies to 5 * Q = -1, contradicts Q > 0
      linarith
  · -- Case where 1 - 2 * Q < 0, so Q > 1/2
    have h2 : abs (1 - 2 * Q) = 2 * Q - 1 := by
      rw [abs_of_neg (lt_of_not_ge h)]
      all_goals linarith
    rw [h2] at hQ1
    cases eq_or_eq_neg_of_abs_eq hQ1 with
    | inl h3 =>
      -- Simplify: 3 * Q - (2 * Q - 1) = 2 
      -- This simplifies to Q = 1, which is valid
      linarith
    | inr h4 =>
      -- Simplify: 3 * Q - (2 * Q - 1) = -2 
      -- This simplifies to Q = -3, contradicts Q > 0
      linarith