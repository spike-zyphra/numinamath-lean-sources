import Mathlib

theorem inequalities_6159 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b + b * c + c * a > 0) :
    (a ^ 2 - b * c) * (b ^ 2 - c * a) / (a + b + 3 * c) +
    (b ^ 2 - c * a) * (c ^ 2 - a * b) / (b + c + 3 * a) +
    (c ^ 2 - a * b) * (a ^ 2 - b * c) / (c + a + 3 * b) ≤ 0 := by

  have ha2 : a + b + 3 * c > 0 := by
    by_contra h'
    push_neg at h'
    have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    have hc0 : c = 0 := by nlinarith
    have h0 : a * b + b * c + c * a = 0 := by nlinarith
    linarith

  have hb1 : b + c + 3 * a > 0 := by
    by_contra h'
    push_neg at h'
    have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    have hc0 : c = 0 := by nlinarith
    have h0 : a * b + b * c + c * a = 0 := by nlinarith
    linarith

  have hc1 : c + a + 3 * b > 0 := by
    by_contra h'
    push_neg at h'
    have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    have hc0 : c = 0 := by nlinarith
    have h0 : a * b + b * c + c * a = 0 := by nlinarith
    linarith

  have ha1' : a + b + 3 * c > 0 := ha2
  have hb1' : b + c + 3 * a > 0 := hb1
  have hc1' : c + a + 3 * b > 0 := hc1

  have h2 : (a ^ 2 - b * c) * (b ^ 2 - c * a) / (a + b + 3 * c) +
      (b ^ 2 - c * a) * (c ^ 2 - a * b) / (b + c + 3 * a) +
      (c ^ 2 - a * b) * (a ^ 2 - b * c) / (c + a + 3 * b) ≤ 0 := by
    have h3 : (a ^ 2 - b * c) * (b ^ 2 - c * a) / (a + b + 3 * c) +
        (b ^ 2 - c * a) * (c ^ 2 - a * b) / (b + c + 3 * a) +
        (c ^ 2 - a * b) * (a ^ 2 - b * c) / (c + a + 3 * b) =
        ((a ^ 2 - b * c) * (b ^ 2 - c * a) * (b + c + 3 * a) * (c + a + 3 * b) +
          (b ^ 2 - c * a) * (c ^ 2 - a * b) * (a + b + 3 * c) * (c + a + 3 * b) +
          (c ^ 2 - a * b) * (a ^ 2 - b * c) * (a + b + 3 * c) * (b + c + 3 * a))
          / ((a + b + 3 * c) * (b + c + 3 * a) * (c + a + 3 * b)) := by
      field_simp
      ring
    rw [h3]
    have h4 : (a + b + 3 * c) * (b + c + 3 * a) * (c + a + 3 * b) > 0 := by positivity
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    all_goals positivity

  exact h2