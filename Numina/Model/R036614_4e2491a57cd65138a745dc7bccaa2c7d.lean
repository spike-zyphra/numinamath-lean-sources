import Mathlib

theorem algebra_100834 {a b : ℝ} (h₀ : a^3-3*a*b^2=39) (h₁ : b^3-3*a^2*b=26) : a^2+b^2=13 := by
  have eq1 : (a^2 + b^2)^3 = 2197 := by
    nlinarith [sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b),
      sq_nonneg (a^2 - 3 * b^2), sq_nonneg (b^2 - 3 * a^2)]
  have eq2 : a^2 + b^2 = 13 := by
    have h2 : (a^2 + b^2)^3 - 2197 = 0 := by linarith
    have h3 : (a^2 + b^2 - 13) * ((a^2 + b^2)^2 + (a^2 + b^2) * 13 + 13^2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · linarith
    · 
      nlinarith [sq_nonneg ((a^2 + b^2) + 13 / 2)]
  exact_mod_cast eq2