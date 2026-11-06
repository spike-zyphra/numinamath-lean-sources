import Mathlib

theorem algebra_290355 {a b c : ℝ} (ha : (a + 1) * (b + 1) * (c + 1) = a * b * c + 1)
    (hb : (a + 2) * (b + 2) * (c + 2) = a * b * c + 2) :
    a = -1 ∧ b = -1 ∧ c = -1 := by
  have eq1 : a * b + a * c + b * c + a + b + c = 0 := by
    nlinarith 
  have eq2 : a * b + a * c + b * c + 2 * a + 2 * b + 2 * c + 3 = 0 := by
    nlinarith 
  have hsum : a + b + c = -3 := by
    nlinarith [eq1, eq2]
  have eq3 : a * b + a * c + b * c = 3 := by
    nlinarith [eq1, hsum]
  have ha1 : a = -1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_self_nonneg (a - b), mul_self_nonneg (b - c), mul_self_nonneg (a - c)]
  have hb1 : b = -1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_self_nonneg (a - b), mul_self_nonneg (b - c), mul_self_nonneg (a - c)]
  have hc1 : c = -1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_self_nonneg (a - b), mul_self_nonneg (b - c), mul_self_nonneg (a - c)]
  exact ⟨ha1, hb1, hc1⟩