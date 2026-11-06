import Mathlib

open Real

theorem algebra_11957 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + 20 * b = 2) (h2 : c + 20 * d = 2) :
    1 / a + 1 / (b * c * d) ≥ 441 / 2 := by
  have h3 : 1 / a + 1 / (b * c * d) - 441 / 2 = ( 2 * (b * c * d) + 2 * a - 441 * (a * (b * c * d)) ) / (2 * a * (b * c * d)) := by
    field_simp
    <;> ring_nf
    <;> field_simp
    all_goals linarith
  have h4 : 0 < 2 * a * (b * c * d) := by positivity
  have h5 : ( 2 * (b * c * d) + 2 * a - 441 * (a * (b * c * d)) ) / (2 * a * (b * c * d)) ≥ 0 := by
    apply div_nonneg
    · -- Prove numerator $\ge 0$
      have hx1 : 2 * (b * c * d) + 2 * a - 441 * (a * (b * c * d)) ≥ 0 := by
        have h7 : c = 2 - 20 * d := by linarith
        have h8 : a = 2 - 20 * b := by linarith
        rw [h7, h8]
        nlinarith [sq_nonneg (b - 2 / 21), sq_nonneg (d - 1 / 20), 
          sq_nonneg (b * d - 2 / 441), 
          sq_nonneg (b - d), 
          mul_pos hb (show 0 < 2 - 20 * b by nlinarith), 
          mul_pos (show 0 < 2 - 20 * b by nlinarith) (show 0 < 2 - 20 * d by nlinarith), 
          mul_pos hd (show 0 < 2 - 20 * d by nlinarith)
          ]
      linarith
    all_goals nlinarith
  linarith [h3, h5]
  all_goals nlinarith