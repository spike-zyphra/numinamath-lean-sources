import Mathlib

theorem algebra_21285 (t1 t2 : ℝ) (ht1 : 6*t1^2+30=41*t1) (ht2 : 6*t2^2+30=41*t2)
    (ht : t1≠t2) : |t1-t2| = 31/6 := by
  have eq1 : 6 * t1^2 - 41 * t1 + 30 = 0 := by linarith
  have eq2 : 6 * t2^2 - 41 * t2 + 30 = 0 := by linarith
  have factored1 : (t1 - 6) * (6 * t1 - 5) = 0 := by
    nlinarith
  have factored2 : (t2 - 6) * (6 * t2 - 5) = 0 := by
    nlinarith
  have ht1_cases : t1 = 6 ∨ t1 = 5 / 6 := by
    cases (mul_eq_zero.mp factored1) with
    | inl h =>
        left
        linarith
    | inr h =>
        right
        linarith
  have ht2_cases : t2 = 6 ∨ t2 = 5 / 6 := by
    cases (mul_eq_zero.mp factored2) with
    | inl h =>
        left
        linarith
    | inr h =>
        right
        linarith
  cases ht1_cases with
  | inl h1 =>
    cases ht2_cases with
    | inl h2 =>
      exfalso
      exact ht (by linarith)
    | inr h2 =>
      rw [h1, h2]
      norm_num [abs_of_nonneg]
  | inr h1 =>
    cases ht2_cases with
    | inl h2 =>
      rw [h1, h2]
      norm_num [abs_of_nonpos]
    | inr h2 =>
      exfalso
      exact ht (by linarith)