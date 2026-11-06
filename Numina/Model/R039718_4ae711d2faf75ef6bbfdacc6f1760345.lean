import Mathlib

open Real Set

theorem inequalities_127172 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    (1 + 1 / a) * (1 + 8 / b) ≥ 50 := by
  have h1 : b = 1 - a := by linarith
  have h2 : a > 0 := ha
  have h3 : b > 0 := hb
  have h4 : a * b > 0 := mul_pos ha hb
  have h5 : (1 + 1 / a) * (1 + 8 / b) - 50 ≥ 0 := by
    have h6 : b = 1 - a := by linarith
    have h7 : 8 * a + b + 8 - 49 * a * b ≥ 0 := by
      rw [show b = 1 - a by linarith]
      have h8 : 49 * a ^ 2 - 42 * a + 9 ≥ 0 := by
        have h9 : 49 * a ^ 2 - 42 * a + 9 = (7 * a - 3) ^ 2 := by ring
        rw [h9]
        have h10 : (7 * a - 3) ^ 2 ≥ 0 := by
          exact sq_nonneg (7 * a - 3)
        nlinarith
      nlinarith
    have h8 : (1 + 1 / a) * (1 + 8 / b) - 50 = (8 * a + b + 8 - 49 * a * b) / (a * b) := by
      field_simp [ha.ne.symm, hb.ne.symm]
      <;> 
      ring_nf
      <;> 
      nlinarith [h]
    rw [h8] at *
    apply div_nonneg
    linarith
    all_goals
    positivity
  linarith