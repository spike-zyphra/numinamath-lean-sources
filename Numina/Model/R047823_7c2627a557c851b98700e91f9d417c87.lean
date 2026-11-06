import Mathlib

theorem algebra_156052 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^3 + b^3 + c^3 - 3 * a * b * c = 0) :
    a = b ∧ b = c := by
  have h1 : (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h1) with h2 h3
  · -- Show that $a + b + c > 0$, deriving a contradiction from $a + b + c = 0$.
    have h2' : a + b + c > 0 := by
      linarith
    linarith
  · -- From $a^2 + b^2 + c^2 - a b - b c - c a = 0$ to $(a-b)^2 + (b-c)^2 + (c-a)^2 = 0$.
    have h4 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
      nlinarith
    have h5 : a - b = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h4]
    have h6 : a = b := by linarith
    have h7 : b - c = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h4]
    have h8 : b = c := by linarith
    exact ⟨h6, h8⟩