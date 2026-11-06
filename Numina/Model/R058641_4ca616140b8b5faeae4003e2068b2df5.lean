import Mathlib

theorem algebra_171398 (x1 x2 k : ℝ) (hroots : x1^2 - (k - 2)*x1 + (k^2 + 3*k + 5) = 0 ∧ x2^2 - (k - 2)*x2 + (k^2 + 3*k + 5) = 0)
    (hx12 : x1 ≠ x2) :
    x1^2 + x2^2 ≤ 18 := by 
  have eq1 : x1^2 - (k - 2)*x1 + (k^2 + 3*k + 5) = 0 := hroots.1
  have eq2 : x2^2 - (k - 2)*x2 + (k^2 + 3*k + 5) = 0 := hroots.2
  have hsum : x1 + x2 = k - 2 := by
    have eq3 : (x1 - x2) * (x1 + x2 - (k - 2)) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp eq3) with
    | inl h =>
      exfalso
      apply hx12
      linarith
    | inr h =>
      linarith

  have hprod : x1 * x2 = k^2 + 3 * k + 5 := by
    have eq3 : x1^2 + x2^2 - (k - 2) * (x1 + x2) + 2 * (k^2 + 3 * k + 5) = 0 := by
      nlinarith [eq1, eq2, hsum]
    nlinarith [sq_nonneg (x1 - x2), hsum]

  have eq3 : x1^2 + x2^2 = (k - 2) ^ 2 - 2 * (k^2 + 3 * k + 5) := by
    nlinarith [hsum, hprod, eq1, eq2]

  have h2 : (k - 2) ^ 2 - 4 * (k^2 + 3 * k + 5) ≥ 0 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hx12), hprod, hsum, eq1, eq2]

  nlinarith [sq_nonneg (k + 4), sq_nonneg (k + 4 / 3), sq_nonneg (k - (-4)), sq_nonneg (k - (-4 / 3)), sq_nonneg (k + 5)]