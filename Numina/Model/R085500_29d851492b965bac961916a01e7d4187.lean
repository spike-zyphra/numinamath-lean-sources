import Mathlib

theorem algebra_140303 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a / (1 + a) + b / (1 + b) = 1) :
    a / (1 + b ^ 2) - b / (1 + a ^ 2) = a - b := by
  have h1 : 0 < (1 + a) * (1 + b) := by positivity
  have eq1 : a * (1 + b) = 1 + a := by
    field_simp [(show 1 + a ≠ 0 by positivity : 1 + a ≠ 0), (show 1 + b ≠ 0 by positivity : 1 + b ≠ 0)] at h ⊢
    nlinarith
  have h2 : a * b = 1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1)]
  have eq2 : a / (1 + b ^ 2) - b / (1 + a ^ 2) = a - b := by
    field_simp [(show 1 + b ^ 2 ≠ 0 by positivity : 1 + b ^ 2 ≠ 0), (show 1 + a ^ 2 ≠ 0 by positivity : 1 + a ^ 2 ≠ 0)]
    <;> nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (a * b - 1), h2, sq_nonneg (a - b), sq_nonneg (a * b)]
  exact eq2