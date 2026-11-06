import Mathlib

theorem inequalities_59692 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
  have h1 : b = 1 - a := by linarith
  rw [h1]
  have h9 : 0 < a := by linarith
  have h10 : 0 < 1 - a := by nlinarith [show a < 1 from by nlinarith [show 0 < b from hb, h]]
  -- need to clear the denominators.
  have h4 : a ^ 4 * (1 - a) ^ 2 + (1 - a) ^ 4 * a ^ 2 + 4 * a ^ 2 * (1 - a) ^ 2 + a ^ 2 + (1 - a) ^ 2 ≥ (25 / 2) * (a ^ 2 * (1 - a) ^ 2) := by 
    have h8 : 0 < a * (1 - a) := by 
      apply mul_pos
      linarith
      nlinarith
    have h9 : 0 < a := by linarith
    have h10 : 0 < 1 - a := by nlinarith [show a < 1 from by nlinarith [show 0 < b from hb, h]]
    -- multiplier for nlinarith
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), sq_nonneg (a * (1 - a) - 1 / 4), sq_nonneg (a - (1 - a)), sq_nonneg (a ^ 2 - (1 - a) ^ 2), sq_nonneg (a * (1 - a)), mul_pos h9 (show 0 < 1 - a by nlinarith), sq_nonneg (a ^ 2 - 1 / 4), sq_nonneg ((1 - a) ^ 2 - 1 / 4)]
  -- introduce the equality to the fractional form.
  have eq1 : (a + 1 / a) ^ 2 + ( (1 - a) + 1 / (1 - a) ) ^ 2 - 25 / 2 = (a ^ 4 * (1 - a) ^ 2 + (1 - a) ^ 4 * a ^ 2 + 4 * a ^ 2 * (1 - a) ^ 2 + a ^ 2 + (1 - a) ^ 2 - (25 / 2) * (a ^ 2 * (1 - a) ^ 2)) / (a ^ 2 * (1 - a) ^ 2) := by
    field_simp [h9, h10]
    ring
  -- finally using the eq1 with h4 to obtain the result.
  have h11 : (a + 1 / a) ^ 2 + ( (1 - a) + 1 / (1 - a) ) ^ 2 ≥ 25 / 2 := by
    have h12 : (a ^ 4 * (1 - a) ^ 2 + (1 - a) ^ 4 * a ^ 2 + 4 * a ^ 2 * (1 - a) ^ 2 + a ^ 2 + (1 - a) ^ 2 - (25 / 2) * (a ^ 2 * (1 - a) ^ 2)) / (a ^ 2 * (1 - a) ^ 2) ≥ 0 := by 
      apply div_nonneg
      linarith [h4]
      positivity
    linarith [eq1, h12]
  exact h11