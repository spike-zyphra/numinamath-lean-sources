import Mathlib

theorem inequalities_308684
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a / (1 + a) + b / (1 + b) + c / (1 + c) = 1) :
    12 ≤ 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 := by 
  have h1 : a > 0 := by linarith
  have h2 : b > 0 := by linarith
  have h3 : c > 0 := by linarith

  have h4 : a * (1 + b) * (1 + c) + b * (1 + a) * (1 + c) + c * (1 + a) * (1 + b) = (1 + a) * (1 + b) * (1 + c) := by 
    have h1' : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
    field_simp [(show 1 + a ≠ 0 by positivity), (show 1 + b ≠ 0 by positivity), (show 1 + c ≠ 0 by positivity)] at h ⊢
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h5 : a * b + a * c + b * c + 2 * a * b * c = 1 := by
    nlinarith

  have h6 : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 - 12 ≥ 0 := by 
    have h7 : 0 < a ^ 2 * b ^ 2 * c ^ 2 := by positivity
    have h8 : (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 - 12) = ( (b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 + a ^ 2 * b ^ 2 - 12 * a ^ 2 * b ^ 2 * c ^ 2) ) / (a ^ 2 * b ^ 2 * c ^ 2) := by
      field_simp
      <;> ring 
    rw [h8]
    have h9 : (b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 + a ^ 2 * b ^ 2 - 12 * a ^ 2 * b ^ 2 * c ^ 2) ≥ 0 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * b + a * c + b * c - 2 * a * b * c),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc]
    apply div_nonneg 
    · linarith 
    · positivity

  linarith