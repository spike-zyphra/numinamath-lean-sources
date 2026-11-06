import Mathlib

theorem algebra_10916 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a^2 / b^2 = 25 / 36) :
    4 * a / (4 * b) = 5 / 6 := by
  have h1 : (a / b) ^ 2 = 25 / 36 := by
    have h2 : a^2 / b^2 = (a / b) ^ 2 := by 
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> linarith
    rw [h2] at h
    linarith
  have h2 : a / b = 5 / 6 := by
    have h3 : 0 < a / b := by 
      apply div_pos
      linarith
      linarith
    have h4 : (a / b) ^ 2 - 25 / 36 = 0 := by 
      linarith [h1]
    have h5 : (a / b - 5 / 6) * (a / b + 5 / 6) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case where $\frac{a}{b} - \frac{5}{6} = 0$, so $\frac{a}{b} = \frac{5}{6}$
      linarith
    · -- Case where $\frac{a}{b} + \frac{5}{6} = 0$, so $\frac{a}{b} = -\frac{5}{6}$, which would be a contradiction
      have h8 : a / b < 0 := by linarith
      linarith [show a / b > 0 from by linarith, h8]
  have h5 : 4 * a / (4 * b) = a / b := by
    field_simp
    <;> ring_nf
    <;> field_simp
  rw [h5, h2]
  <;> linarith
  all_goals linarith