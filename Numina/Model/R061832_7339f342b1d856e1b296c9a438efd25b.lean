import Mathlib

open Real Set

theorem algebra_603176 (a b : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hab : a * b = 1 / 36) :
    1 / (1 - a) + 1 / (1 - b) ≥ 12 / 5 := by
  have ha1 : 0 < a := ha.1
  have ha2 : a < 1 := ha.2
  have hb1 : 0 < b := hb.1
  have hb2 : b < 1 := hb.2
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - b := by linarith
  have h4 : 0 < (1 - a) * (1 - b) := by
    apply mul_pos
    all_goals linarith
  have h3 : a + b ≥ 1 / 3 := by
    nlinarith [sq_nonneg (a - b), hab, mul_pos ha1 hb1]
  have h5 : 5 * (2 - (a + b)) - 12 * (1 - a) * (1 - b) ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1 / 6), sq_nonneg (b - 1 / 6), hab, h3]
  have h6 : 1 / (1 - a) + 1 / (1 - b) - 12 / 5 ≥ 0 := by
    have h9 : (1 / (1 - a) + 1 / (1 - b) - 12 / 5) =
        (5 * (2 - (a + b)) - 12 * (1 - a) * (1 - b)) / (5 * (1 - a) * (1 - b)) := by
      field_simp
      ring
    rw [h9]
    apply div_nonneg
    linarith
    positivity
  linarith