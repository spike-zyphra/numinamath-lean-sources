import Mathlib

open Real

theorem inequalities_3754
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b + c = 1) :
    (1 + 1 / a) * (1 + 1 / b) * (1 + 1 / c) ≥ 64 := by
  have ha1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h1 : (1 + 1 / a) * (1 + 1 / b) * (1 + 1 / c) - 64 ≥ 0 := by
    have h2 : (1 + 1 / a) * (1 + 1 / b) * (1 + 1 / c) - 64 =
        ((a + 1) * (b + 1) * (c + 1) - 64 * (a * b * c)) / (a * b * c) := by
      field_simp
      ring
    rw [h2]
    have h3 : (a + 1) * (b + 1) * (c + 1) - 64 * (a * b * c) ≥ 0 := by
      have h4 : c = 1 - a - b := by linarith
      rw [h4]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b)), 
          mul_pos ha hb, mul_pos hb (show 0 < 1 - a - b by nlinarith [h, ha, hb, hc]), 
          mul_pos ha (show 0 < 1 - a - b by nlinarith [h, ha, hb, hc]), 
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - (1 - a - b) * a), sq_nonneg ((1 - a - b) * a - a * b)
      ]
    have ha2 : a * b * c > 0 := by positivity
    apply div_nonneg
    · linarith
    · positivity
  linarith