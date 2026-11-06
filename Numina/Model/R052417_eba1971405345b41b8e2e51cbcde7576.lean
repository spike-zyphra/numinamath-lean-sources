import Mathlib

theorem inequalities_315889 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) = 1) :
    a * b + b * c + c * a ≤ a + b + c := by
  have h1 : a + b + 1 ≠ 0 := by positivity
  have h2 : b + c + 1 ≠ 0 := by positivity
  have h3 : c + a + 1 ≠ 0 := by positivity
  field_simp [h1, h2, h3] at h
  ring_nf at h
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
         mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
         sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
  <;> nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
         mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
         sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
  <;> nlinarith
  <;> ring_nf at h
  <;> nlinarith
  all_goals
    ring_nf at h ⊢
    all_goals
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]