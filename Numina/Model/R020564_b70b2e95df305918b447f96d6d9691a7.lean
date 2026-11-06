import Mathlib
import Aesop

theorem inequalities_600561 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 / (a + b)) + (b^2 / (b + c)) + (c^2 / (c + a)) ≥ (a + b + c) / 2 := by
  have h1 : (a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a)) - (a + b + c) / 2 ≥ 0 := by
    have h2 : 2 * a^2 * (b + c) * (c + a) + 2 * b^2 * (a + b) * (c + a) + 2 * c^2 * (a + b) * (b + c) - (a + b + c) * (a + b) * (b + c) * (c + a) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b) + b * (b - c) + c * (c - a)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (show 0 < b + c by linarith) (show 0 < c + a by linarith),
          mul_pos (show 0 < c + a by linarith) (show 0 < a + b by linarith),
          mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith)]
    have h3 : (a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a)) - (a + b + c) / 2 =
        (2 * a^2 * (b + c) * (c + a) + 2 * b^2 * (a + b) * (c + a) + 2 * c^2 * (a + b) * (b + c) - (a + b + c) * (a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a)) := by
      field_simp
      ring
    have h4 : 0 < 2 * (a + b) * (b + c) * (c + a) := by
      have h11 : 0 < a + b := by nlinarith
      have h12 : 0 < b + c := by nlinarith
      have h13 : 0 < c + a := by nlinarith
      positivity
    rw [h3]
    apply div_nonneg
    linarith
    all_goals nlinarith
  linarith [h1]