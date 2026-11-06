import Mathlib

open Real

theorem inequalities_244561 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : c + a > b) (h'' : b + c > a) :
    3 ≤ (b + c - a) / a + (c + a - b) / b + (a + b - c) / c ∧
    (b + c - a) / a + (c + a - b) / b + (a + b - c) / c ≤
    a / (b + c - a) + b / (c + a - b) + c / (a + b - c) := by
  constructor
  · -- Prove 3 ≤ (b + c - a) / a + (c + a - b) / b + (a + b - c) / c
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals
        linarith
    have h2 : (b + c - a) / a + (c + a - b) / b + (a + b - c) / c ≥ 3 := by
      have pos1 : 0 < a := by linarith
      have pos2 : 0 < b := by linarith
      have pos3 : 0 < c := by linarith
      have h3 : (b + c - a) / a + (c + a - b) / b + (a + b - c) / c - 3 ≥ 0 := by
        have pos4 : 0 < a * b * c := by positivity
        have h4 : (b + c - a) / a + (c + a - b) / b + (a + b - c) / c - 3 =
                ((b + c - a) * (b * c) + (c + a - b) * (a * c) + (a + b - c) * (a * b) - 3 * (a * b * c)) / (a * b * c) := by
          field_simp
          ring
        rw [h4] at *
        apply div_nonneg
        have h5 : (b + c - a) * (b * c) + (c + a - b) * (a * c) + (a + b - c) * (a * b) - 3 * (a * b * c) ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
                sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
                sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
              ]
        linarith
        all_goals
          positivity
      linarith
    linarith
  · -- Prove (b + c - a) / a + (c + a - b) / b + (a + b - c) / c ≤ a / (b + c - a) + b / (c + a - b) + c / (a + b - c)
    have pos1 : 0 < b + c - a := by linarith
    have pos2 : 0 < c + a - b := by linarith
    have pos3 : 0 < a + b - c := by linarith
    have h3 : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - ((b + c - a) / a + (c + a - b) / b + (a + b - c) / c) ≥ 0 := by
      have h4 : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - ((b + c - a) / a + (c + a - b) / b + (a + b - c) / c) =
              ( (a^2 * (c + a - b) * (a + b - c) * b * c) +
                (b^2 * (b + c - a) * (a + b - c) * a * c) +
                (c^2 * (b + c - a) * (c + a - b) * a * b) -
                ( (b + c - a)^2 * (c + a - b) * (a + b - c) * b * c) -
                ( (c + a - b)^2 * (b + c - a) * (a + b - c) * a * c) -
                ( (a + b - c)^2 * (b + c - a) * (c + a - b) * a * b)
              ) / (a * b * c * (b + c - a) * (c + a - b) * (a + b - c)) := by
        field_simp
        ring
      rw [h4] at *
      have pos4 : 0 < a * b * c * (b + c - a) * (c + a - b) * (a + b - c) := by
        positivity
      have h5 : (a^2 * (c + a - b) * (a + b - c) * b * c) +
                (b^2 * (b + c - a) * (a + b - c) * a * c) +
                (c^2 * (b + c - a) * (c + a - b) * a * b) -
                ( (b + c - a)^2 * (c + a - b) * (a + b - c) * b * c) -
                ( (c + a - b)^2 * (b + c - a) * (a + b - c) * a * c) -
                ( (a + b - c)^2 * (b + c - a) * (c + a - b) * a * b) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
              sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
              sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
              mul_pos (show 0 < b + c - a from by linarith) (show 0 < c + a - b from by linarith),
              mul_pos (show 0 < c + a - b from by linarith) (show 0 < a + b - c from by linarith),
              mul_pos (show 0 < b + c - a from by linarith) (show 0 < a + b - c from by linarith),
              sq_nonneg (a * (b + c - a) - b * (c + a - b)), sq_nonneg (b * (c + a - b) - c * (a + b - c)), sq_nonneg (c * (a + b - c) - a * (b + c - a))
            ]
      have h8 : ( (a^2 * (c + a - b) * (a + b - c) * b * c) +
                (b^2 * (b + c - a) * (a + b - c) * a * c) +
                (c^2 * (b + c - a) * (c + a - b) * a * b) -
                ( (b + c - a)^2 * (c + a - b) * (a + b - c) * b * c) -
                ( (c + a - b)^2 * (b + c - a) * (a + b - c) * a * c) -
                ( (a + b - c)^2 * (b + c - a) * (c + a - b) * a * b)
              ) / (a * b * c * (b + c - a) * (c + a - b) * (a + b - c)) ≥ 0 := by
        apply div_nonneg
        linarith
        all_goals
        positivity
      linarith
    linarith