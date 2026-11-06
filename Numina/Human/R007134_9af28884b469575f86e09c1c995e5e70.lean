import Mathlib

/- Find the sum of the coefficients in the polynomial $3(3x^{7} + 8x^4 - 7) + 7(x^5 - 7x^2 + 5)$ when it is fully simplified. -/
theorem algebra_10629 {f : Polynomial ℤ} (hf : f = 3 * (3 * Polynomial.X ^ 7 + 8 * Polynomial.X ^ 4 - 7) + 7 * (Polynomial.X ^ 5 - 7 * Polynomial.X ^ 2 + 5)) :
    f.eval 1 = 5 := by
  -- simplify
  have hf': f = 9*Polynomial.X^7 + 7*Polynomial.X^5 + 24*Polynomial.X^4 - 49*Polynomial.X^2 + 14 := by
    rw [hf]; ring
  -- sum of coefficients equal value at X=1
  rw [hf']
  -- sum = f(1) = 9+7+24-49+14=5
  simp