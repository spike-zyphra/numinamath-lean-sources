import Mathlib

theorem algebra_1914
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 := by
--     For $\frac{a}{b+c} \geq 0$ in Lean's expression.
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * c := mul_pos ha hc
  have h3 : 0 < b * c := mul_pos hb hc
--     Multiply all denominators (b+c), (a+c), (a+b). So multiply all denominators.
--     Therefore, we need to multiply by (b + c) * (a + c) * (a + b).
--     To clear denominators.
  have h6 : 0 < (b + c) * (a + c) * (a + b) := by
    positivity
--     From above multiplied.
  have h4 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h5 : (a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2) =
        (2 * (a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c)) - 3 * (b + c) * (a + c) * (a + b)) / (2 * (b + c) * (a + c) * (a + b)) := by
      field_simp
      ring
    rw [h5]
--     Multiply numerators and denominators.
    apply div_nonneg
--     Need to prove that the numerator is greater than 0.
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), sq_nonneg (a * (a - b + c)), sq_nonneg (b * (b - c + a)), sq_nonneg (c * (c - a + b)), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), sq_nonneg (a * (a - b + c)), sq_nonneg (b * (b - c + a)), sq_nonneg (c * (c - a + b)), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (b * (a - c)), sq_nonneg (c * (b - a)), sq_nonneg (a - b + c), sq_nonneg (b - c + a), sq_nonneg (c - a + b)
          ]
--     positivity of denominator
    positivity
--     Now we have the inequality.
  nlinarith
--     We need to clear denominators. Therefore, multiply numerators. Multiply denominators.
--     So:
--     Therefore. rewrite as above.
  all_goals nlinarith
  all_goals nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a * (a - b + c)), sq_nonneg (b * (b - c + a)), sq_nonneg (c * (c - a + b))]
  all_goals ring
  all_goals linarith
  all_goals linarith [ha, hb, hc]
  all_goals ring
  all_goals ring
  all_goals positivity