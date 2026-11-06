import Mathlib

/-
37. (POL 2) Prove that for arbitrary positive numbers the following inequality holds:
$$
\frac{1}{a}+\frac{1}{b}+\frac{1}{c} \leq \frac{a^{8}+b^{8}+c^{8}}{a^{3} b^{3} c^{3}} .
$$
-/
theorem inequalities_254430 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
1 / a + 1 / b + 1 / c ≤ (a^8 + b^8 + c^8) / (a^3 * b^3 * c^3) := by

/- First, confirm that the product of a, b, c is positive since each number is positive.
   This ensures our denominators will be valid. -/
have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
have h2 : a^3 * b^3 * c^3 > 0 := by
  apply mul_pos
  apply mul_pos
  · exact pow_pos ha 3
  · exact pow_pos hb 3
  · exact pow_pos hc 3

-- Rewrite the fraction as a product with reciprocal to prepare for later steps
have h3 : (a^8 + b^8 + c^8) / (a^3 * b^3 * c^3) = (a^8 + b^8 + c^8) * (1 / (a^3 * b^3 * c^3)) := by
  field_simp
rw [h3]

-- We'll prove that the difference between RHS and LHS is nonnegative
have h4 : (1 / a + 1 / b + 1 / c) ≤ (a^8 + b^8 + c^8) * (1 / (a^3 * b^3 * c^3)) := by
  have h5 : (a^8 + b^8 + c^8) * (1 / (a^3 * b^3 * c^3)) - (1 / a + 1 / b + 1 / c) ≥ 0 := by
    /- Use a series of square nonnegativity properties to prove that
      a^8 + b^8 + c^8 - (a^2 * b^3 * c^3 + a^3 * b^2 * c^3 + a^3 * b^3 * c^2) ≥ 0,
      which is the AM-GM inequality part -/
    have h6 : a^8 + b^8 + c^8 - (a^2 * b^3 * c^3 + a^3 * b^2 * c^3 + a^3 * b^3 * c^2) ≥ 0 := by 
      nlinarith [sq_nonneg (a^4 - b^4), sq_nonneg (b^4 - c^4), sq_nonneg (c^4 - a^4),
        sq_nonneg (a^4 - b^3 * c), sq_nonneg (b^4 - a^3 * c), sq_nonneg (c^4 - a^3 * b),
        sq_nonneg (a^2 * b^2 - a * b * c^2), sq_nonneg (a^2 * c^2 - a * b^2 * c),
        sq_nonneg (b^2 * c^2 - a^2 * b * c), sq_nonneg (a^3 - b^3), sq_nonneg (b^3 - c^3),
        sq_nonneg (c^3 - a^3), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    
    /- Transform the difference into a fraction and prove it's nonnegative
      using the fact that numerator is nonnegative and denominator is positive. -/
    have h7 : (a^8 + b^8 + c^8) * (1 / (a^3 * b^3 * c^3)) - (1 / a + 1 / b + 1 / c) = 
      (a^8 + b^8 + c^8 - (a^2 * b^3 * c^3 + a^3 * b^2 * c^3 + a^3 * b^3 * c^2)) / (a^3 * b^3 * c^3) := by 
      field_simp
      ring
    rw [h7]
    have h8 : a^3 * b^3 * c^3 > 0 := by 
      apply mul_pos
      apply mul_pos
      · exact pow_pos ha 3
      · exact pow_pos hb 3
      · exact pow_pos hc 3
    apply div_nonneg
    · linarith
    · linarith
  linarith
linarith