import Mathlib

theorem algebra_284763 {a : ℕ → ℝ} {x0 : ℝ}
    (h1 : x0^4 + a 0 * x0^3 + a 1 * x0^2 + a 2 * x0 + a 3 = 0)
    (h2 : 4 * x0^3 + 3 * a 0 * x0^2 + 2 * a 1 * x0 + a 2 = 0) :
    (X - x0)^2 ∣ X^4 + a 0 * X^3 + a 1 * X^2 + a 2 * X + a 3 := by
  use X^2 + (a 0 + 2 * x0) * X + (a 1 + 2 * (a 0) * x0 + 3 * x0 ^ 2)
  have eq1 : a 2 = -4 * x0 ^ 3 - 3 * (a 0) * x0 ^ 2 - 2 * (a 1) * x0 := by
    linarith 
  have eq2 : a 3 = -x0 ^ 4 - (a 0) * x0 ^ 3 - (a 1) * x0 ^ 2 - (a 2) * x0 := by 
    linarith 
  rw [eq1] at *
  rw [eq2] at *
  ring_nf
  <;> simp [mul_add, add_mul, mul_assoc, pow_two, mul_comm, mul_left_comm]
  <;> ring_nf <;> 
    nlinarith [sq_nonneg (X - x0), sq_nonneg (X^2 - x0^2), sq_nonneg (X - x0), sq_nonneg (X + x0), sq_nonneg (x0)]