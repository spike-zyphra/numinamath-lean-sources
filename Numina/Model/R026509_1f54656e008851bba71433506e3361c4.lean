import Mathlib

theorem algebra_192183 {p1 p2 q1 q2 : ℝ} (h : p1 * p2 = 2 * (q1 + q2)) :
    ∃ x : ℝ, x^2 + p1 * x + q1 = 0 ∨ x^2 + p2 * x + q2 = 0 := by
  by_cases h1 : p1 ^ 2 - 4 * q1 ≥ 0
  · -- If the first quadratic has real roots, we are done
    use (-p1 + Real.sqrt (p1 ^ 2 - 4 * q1)) / 2
    left
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by nlinarith)]
    <;> linarith
  · -- If the first quadratic does not have real roots, then we have to show that the second one does.
    have h2 : p2 ^ 2 - 4 * q2 ≥ 0 := by
      nlinarith [sq_nonneg (p1 - p2), sq_nonneg (p1 + p2), sq_nonneg (q1 - q2), sq_nonneg (q1 + q2), sq_nonneg (p1 ^ 2 - 4 * q1), sq_nonneg (p2 ^ 2 - 4 * q2), sq_nonneg (p1 - 2), sq_nonneg (p2 - 2)]
    use (-p2 + Real.sqrt (p2 ^ 2 - 4 * q2)) / 2
    right
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by nlinarith)]
    <;> linarith