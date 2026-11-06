import Mathlib

theorem algebra_284690 {x : ℝ} (hx : x > 0) (h : x^10 + x^5 + 1/x^5 + 1/x^10 = 15250) :
    x + 1/x = 3 := by
  have hx1 : x + 1/x > 0 := by
    have hx2 : x > 0 := hx
    have hx3 : 1 / x > 0 := by positivity
    linarith
  have h1 : x^10 + 1/x^10 = (x^5 + 1/x^5)^2 - 2 := by
    field_simp
    <;> ring
  have eq2 : (x^5 + 1/x^5)^2 + (x^5 + 1/x^5) - 15252 = 0 := by
    have eq3 : x^10 + 1/x^10 + x^5 + 1/x^5 = 15250 := by
      have h1 : x^10 + x^5 + 1/x^5 + 1/x^10 = 15250 := h
      nlinarith
    rw [h1] at eq3
    nlinarith
  have h2 : x^5 + 1/x^5 = 123 := by
    have h3 : (x^5 + 1/x^5)^2 + (x^5 + 1/x^5) - 15252 = 0 := eq2
    have h4 : (x^5 + 1/x^5 + 1/2)^2 = (247/2)^2 := by
      nlinarith
    have h5 : x^5 + 1/x^5 = 123 := by
      nlinarith [show (x^5 + 1/x^5) > 0 by
        have h6 : x^5 > 0 := by positivity
        have h7 : 1 / x^5 > 0 := by positivity
        linarith
      ]
    assumption
  have eq4 : (x + 1/x)^5 = x^5 + 1/x^5 + 5*(x^3 + 1/x^3) + 10*(x + 1/x) := by 
    field_simp
    <;> ring_nf
  have eq5 : x^3 + 1/x^3 = (x + 1/x)^3 - 3*(x + 1/x) := by
    field_simp
    <;> ring_nf
  have eq6 : (x + 1/x)^5 - 5*(x + 1/x)^3 + 5*(x + 1/x) = 123 := by
    rw [eq4, eq5] 
    nlinarith [h2]
  have h3 : (x + 1/x - 3) * ((x + 1/x)^4 + 3*(x + 1/x)^3 - 4*(x + 1/x)^2 - 12*(x + 1/x) + 41) = 0 := by
    nlinarith [sq_nonneg ((x + 1/x)^2 - 9), sq_nonneg ((x + 1/x) - 3), sq_nonneg ((x + 1/x) + 3), mul_pos hx (show 0 < x by linarith)]
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case $x + \frac{1}{x} - 3 = 0$, so $x + \frac{1}{x} = 3$.
    linarith
  · -- Case $(x + \frac{1}{x})^4 + 3(x + \frac{1}{x})^3 - 4(x + \frac{1}{x})^2 - 12(x + \frac{1}{x}) + 41 = 0$.
    have h4 : (x + 1/x)^4 + 3*(x + 1/x)^3 - 4*(x + 1/x)^2 - 12*(x + 1/x) + 41 > 0 := by
      nlinarith [sq_nonneg ((x + 1/x)^2 - 9/4), sq_nonneg ((x + 1/x) - 3/2), sq_nonneg ((x + 1/x) + 3/2), mul_pos hx (show 0 < x by linarith), sq_nonneg ((x + 1/x)^2 - 25/4), sq_nonneg ((x + 1/x) - 2), sq_nonneg ((x + 1/x) + 2)]
    nlinarith