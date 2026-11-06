import Mathlib

theorem inequalities_88026 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
     a/(b+c)+b/(c+a)+c/(a+b)≥(a+b)/(a+b+2*c)+ (b+c)/(2*a+b+c)+ (c+a)/(a+2*b+c) := by
  have h1 : 0 < (b + c) * (c + a) * (a + b) * (a + b + 2 * c) * (2 * a + b + c) * (a + 2 * b + c) := by
    positivity

  have h2 : a / (b + c) + b / (c + a) + c / (a + b) - ((a + b) / (a + b + 2 * c) + (b + c) / (2 * a + b + c) + (c + a) / (a + 2 * b + c)) ≥ 0 := by
    have pos1 : 0 < (b + c) * (c + a) * (a + b) * (a + b + 2 * c) * (2 * a + b + c) * (a + 2 * b + c) := by
      positivity
    have h3 : a / (b + c) + b / (c + a) + c / (a + b) - ((a + b) / (a + b + 2 * c) + (b + c) / (2 * a + b + c) + (c + a) / (a + 2 * b + c)) =
        (a * (c + a) * (a + b) * (a + b + 2 * c) * (2 * a + b + c) * (a + 2 * b + c) +
            b * (b + c) * (a + b) * (a + b + 2 * c) * (2 * a + b + c) * (a + 2 * b + c) +
            c * (b + c) * (c + a) * (a + b + 2 * c) * (2 * a + b + c) * (a + 2 * b + c) -
            (a + b) * (b + c) * (c + a) * (a + b) * (2 * a + b + c) * (a + 2 * b + c) -
            (b + c) * (b + c) * (c + a) * (a + b) * (a + b + 2 * c) * (a + 2 * b + c) -
            (c + a) * (b + c) * (c + a) * (a + b) * (a + b + 2 * c) * (2 * a + b + c)) / ((b + c) * (c + a) * (a + b) * (a + b + 2 * c) * (2 * a + b + c) * (a + 2 * b + c)) := by
      field_simp
      ring
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
    all_goals positivity

  linarith