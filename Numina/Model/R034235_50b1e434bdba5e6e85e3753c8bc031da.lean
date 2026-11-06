import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem inequalities_8321 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  3 * (a^2 + b^2 + c^2) / (a + b + c) ≥ (a^2 + b^2) / (a + b) + (b^2 + c^2) / (b + c) + (c^2 + a^2) / (c + a) := by
  have habc : 0 < a + b + c := by
    linarith
  have hab : 0 < a + b := by
    nlinarith
  have hbc : 0 < b + c := by
    nlinarith
  have hca : 0 < c + a := by
    nlinarith
  have h1 : 0 < a + b + c := by linarith
  have h2 : 0 < a + b := by linarith
  have h3 : 0 < b + c := by linarith
  have h4 : 0 < c + a := by linarith
  have h5 : 3 * (a^2 + b^2 + c^2) / (a + b + c) - ((a^2 + b^2) / (a + b) + (b^2 + c^2) / (b + c) + (c^2 + a^2) / (c + a)) ≥ 0 := by
    have pos1 : 0 < (a + b + c) * (a + b) * (b + c) * (c + a) := by positivity
    have eq1 : 3 * (a^2 + b^2 + c^2) / (a + b + c) - ((a^2 + b^2) / (a + b) + (b^2 + c^2) / (b + c) + (c^2 + a^2) / (c + a)) =
      (3 * (a^2 + b^2 + c^2) * (a + b) * (b + c) * (c + a) - ((a^2 + b^2) * (a + b + c) * (b + c) * (c + a) + (b^2 + c^2) * (a + b + c) * (a + b) * (c + a) + (c^2 + a^2) * (a + b + c) * (a + b) * (b + c))) / ((a + b + c) * (a + b) * (b + c) * (c + a)) := by 
      field_simp
      <;> ring
    rw [eq1] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc),
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c * a from mul_pos hc ha),
      mul_pos (show 0 < b * c from mul_pos hb hc) (show 0 < c * a from mul_pos hc ha)
    ]
    all_goals
      positivity
  linarith