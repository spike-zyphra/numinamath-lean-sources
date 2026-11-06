import Mathlib

theorem algebra_327197 {p q : ℝ} (h : p^2 + 1 ≤ 4 * q + 2 * p) (f : ℝ → ℝ)
    (hf : ∀ x, f x = x^2 + p * x + q) :
    {x | f x = x} = {x | f (f x) = x} := by
  ext x
  simp only [hf, Set.mem_setOf_eq]
  constructor
  · -- Assume f x = x, prove f (f x) = x
    intro h_eq
    have eq1 : (x ^ 2 + p * x + q) ^ 2 + p * (x ^ 2 + p * x + q) + q = x := by
      have eq2 : x ^ 2 + p * x + q = x := by linarith
      have eq3 : (x ^ 2 + p * x + q) ^ 2 + p * (x ^ 2 + p * x + q) + q = x := by
        rw [show x ^ 2 + p * x + q = x by linarith]
        all_goals nlinarith
      exact_mod_cast eq3
    linarith [eq1]
  · -- Assume f(f(x)) = x, prove f(x) = x
    intro h_eq
    have h1 : (x^2 + p * x + q) ^ 2 + p * (x^2 + p * x + q) + q = x := by
      nlinarith
    have h2 : (p - 1) ^ 2 ≤ 4 * q := by nlinarith
    have h3 : (x^2 + p * x + q - x) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (x^2 + p * x + q - x), sq_nonneg (x + p / 2 - 1 / 2), sq_nonneg (p - 1), sq_nonneg (q - (p ^ 2) / 4),
        sq_nonneg (x - (1 - p) / 2)]
    have h4 : x^2 + p * x + q - x = 0 := by
      nlinarith [sq_nonneg (x^2 + p * x + q - x), sq_nonneg (x + p / 2 - 1 / 2), sq_nonneg (p - 1), sq_nonneg (q - (p ^ 2) / 4),
        sq_nonneg (x - (1 - p) / 2)]
    linarith