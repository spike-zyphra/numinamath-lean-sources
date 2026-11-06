import Mathlib

theorem algebra_316335 {x : ℝ} (hx : x > 0) (h : x^3 + 1 / x^3 + x^6 + 1 / x^6 = 2754) :
    x + 1 / x = 4 := by
  -- First note that x^6 + 1/x^6 = (x^3 + 1/x^3)^2 - 2.
  have h1 : x^6 + 1 / x^6 = (x^3 + 1 / x^3) ^ 2 - 2 := by
    field_simp
    ring
  -- Rewrite the given equation in terms of y = x^3 + 1/x^3
  -- We have y + (y^2 - 2) = 2754, which results in a quadratic.
  have h2 : (x^3 + 1 / x^3) ^ 2 + (x^3 + 1 / x^3) - 2756 = 0 := by
    have eq1 : x^3 + 1 / x^3 + (x^6 + 1 / x^6) = 2754 := by
      linarith
    rw [h1] at eq1
    nlinarith
  -- Solving the quadratic equation y^2 + y - 2756 = 0.
  -- The discriminant is 1 + 4 * 2756 = 11025 = 105^2. The solution is 52.
  have h3 : x^3 + 1 / x^3 = 52 := by
    have h4 : (x^3 + 1 / x^3) ^ 2 + (x^3 + 1 / x^3) - 2756 = 0 := h2
    have h5 : (x^3 + 1 / x^3 - 52) * (x^3 + 1 / x^3 + 53) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- First case: x^3 + 1/x^3 -52 =0, so x^3 +1/x^3=52.
      linarith
    · -- Second case: x^3 +1/x^3 +53=0. This is invalid since x>0.
      have h8 : x^3 + 1 / x^3 > 0 := by
        have h9 : x^3 > 0 := by
          positivity
        have h10 : (1 / x^3 : ℝ) > 0 := by
          positivity
        linarith
      nlinarith
  -- Now, solve for x + 1/x from x^3 +1/x^3 = 52.
  -- We know that x^3 +1/x^3 = (x +1/x)^3 -3(x +1/x).
  -- Solving gives a cubic equation. Real solution is z = 4.
  have h4 : (x + 1 / x) ^ 3 - 3 * (x + 1 / x) - 52 = 0 := by
    have eq1 : x^3 + 1 / x^3 = 52 := h3
    have eq2 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      field_simp
      ring
    rw [eq2] at eq1
    linarith
  -- Factored into (x +1/x -4)(polynomial)=0, where polynomial >0.
  have h5 : (x + 1 / x - 4) * ((x + 1 / x) ^ 2 + 4 * (x + 1 / x) + 13) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- First case: x +1/x =4.
    linarith
  · -- Second case: (x +1/x)^2+4(x +1/x)+13=0, invalid.
    have h8 : (x + 1 / x) ^ 2 + 4 * (x + 1 / x) + 13 > 0 := by
      nlinarith [sq_nonneg (x + 1 / x + 2)]
    nlinarith [sq_nonneg (x + 1 / x + 2)]