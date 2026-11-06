import Mathlib

theorem algebra_126896 {a b : ℝ} (ha : a^3-3*a*b^2=11) (hb : b^3-3*a^2*b=2) :
    a^2+b^2=5 := by
  have h1 : (a^3 - 3 * a * b^2)^2 + (b^3 - 3 * a^2 * b)^2 = 125 := by
    nlinarith [sq_nonneg (a^3 - 3 * a * b^2 - 11), sq_nonneg (b^3 - 3 * a^2 * b - 2), ha, hb]
  have h2 : (a^3 - 3 * a * b^2)^2 + (b^3 - 3 * a^2 * b)^2 = (a^2 + b^2)^3 := by
    nlinarith [sq_nonneg (a * b), sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - b^3), sq_nonneg (a^5 - b^5)]
  have h3 : (a^2 + b^2)^3 = 125 := by
    nlinarith [h2, h1]
  have h4 : a^2 + b^2 ≥ 0 := by
    nlinarith [sq_nonneg a, sq_nonneg b]
  have h5 : a^2 + b^2 = 5 := by
    have h6 : (a^2 + b^2)^3 = 5^3 := by 
      nlinarith [h3]
    have h7 : a^2 + b^2 = 5 := by
      have h8 : (a^2 + b^2 - 5) * ((a^2 + b^2)^2 + (a^2 + b^2)*5 + 25) = 0 := by
        ring_nf at h6 ⊢
        nlinarith 
      cases' (mul_eq_zero.1 h8) with h9 h10
      · -- First factor is zero
        nlinarith
      · -- Show that the second factor is not zero
        nlinarith [sq_nonneg (a^2 + b^2 - 5 / 2), sq_nonneg (a^2 + b^2 + 5 / 2)]
    exact h7
  exact h5