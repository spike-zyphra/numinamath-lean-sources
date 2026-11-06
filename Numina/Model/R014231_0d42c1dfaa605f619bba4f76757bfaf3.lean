import Mathlib

open Real Set

theorem inequalities_311895 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) := by
  have pos1 : 0 < 2 * a + 1 := by nlinarith
  have pos2 : 0 < 2 * b + 1 := by nlinarith
  have pos3 : 0 < 2 * c + 1 := by nlinarith
  have h3 : (2 * b + 1) * (2 * c + 1) + (2 * a + 1) * (2 * c + 1) + (2 * a + 1) * (2 * b + 1) ≥ (2 * a + 1) * (2 * b + 1) * (2 * c + 1) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
              habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
            ]
  have h4 : (1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1) ≥ 0 := by
    have pos1 : 0 < 2 * a + 1 := by nlinarith
    have pos2 : 0 < 2 * b + 1 := by nlinarith
    have pos3 : 0 < 2 * c + 1 := by nlinarith
    have h5 : (1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1) = ((2 * b + 1) * (2 * c + 1) + (2 * a + 1) * (2 * c + 1) + (2 * a + 1) * (2 * b + 1) - (2 * a + 1) * (2 * b + 1) * (2 * c + 1)) / ((2 * a + 1) * (2 * b + 1) * (2 * c + 1)) := by
      field_simp [show 0 < 2 * a + 1 by linarith, show 0 < 2 * b + 1 by linarith, show 0 < 2 * c + 1 by linarith]
      <;> ring
    rw [h5]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith