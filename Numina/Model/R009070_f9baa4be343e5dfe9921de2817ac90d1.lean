import Mathlib

theorem algebra_13099 (x : ℚ) : abs (x - 3) = 2 * x + 4 ↔ x = -1 / 3 := by
  constructor
  · -- Forward direction: If abs (x - 3) = 2 * x + 4, then x = -1/3
    intro h
    cases abs_cases (x - 3) with
    | inl h1 =>
      linarith
    | inr h2 =>
      linarith
  · -- Backward direction: If x = -1/3, then abs (x - 3) = 2 * x + 4
    intro h_eq
    rw [h_eq]
    norm_num [abs_of_nonneg, abs_of_neg]