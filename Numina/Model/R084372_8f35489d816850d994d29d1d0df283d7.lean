import Mathlib

theorem algebra_94851 {a b : ℝ} (ha : a > 0) (hb : b > 0)
    (h1 : (a + b) / 2 = 6) (h2 : Real.sqrt (a * b) = 10) :
    (X ^ 2 - 12 * X + 100 : Polynomial ℝ).eval a = 0 ∧
    (X ^ 2 - 12 * X + 100 : Polynomial ℝ).eval b = 0 := by
  have hab : a + b = 12 := by
    linarith
  have hab2 : a * b = 100 := by
    have h3 : Real.sqrt (a * b) = 10 := h2
    have h4 : (Real.sqrt (a * b)) ^ 2 = 10 ^ 2 := by rw [h3]
    rw [Real.sq_sqrt (by positivity)] at h4
    nlinarith
  have h3 : a ^ 2 - 12 * a + 100 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 12)]
  have h4 : b ^ 2 - 12 * b + 100 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 12)]
  constructor
  · -- Show that a is a root of the polynomial X^2 - 12X + 100
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith [h3]
  · -- Show that b is a root of the polynomial X^2 - 12X + 100
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith [h4]