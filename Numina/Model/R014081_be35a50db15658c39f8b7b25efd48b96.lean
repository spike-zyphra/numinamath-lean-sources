import Mathlib


open Real


lemma lemma_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 9 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith),
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith),
          mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)
          ]




theorem inequalities_598272 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * (a^3 + b^3 + c^3) / (a * b * c) + 9 * (a + b + c)^2 / (a^2 + b^2 + c^2) ≥ 33 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h3 : 2 * (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) + 9 * (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2) - 33 ≥ 0 := by
    have pos1 : 0 < a * b * c := by positivity
    have pos2 : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
    have h4 : 2 * (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) + 9 * (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2) - 33 =
        (2 * (a ^ 3 + b ^ 3 + c ^ 3) * (a ^ 2 + b ^ 2 + c ^ 2) + 9 * (a + b + c) ^ 2 * (a * b * c) - 33 * (a * b * c) * (a ^ 2 + b ^ 2 + c ^ 2)) / ((a * b * c) * (a ^ 2 + b ^ 2 + c ^ 2)) := by
      field_simp
      ring
    rw [h4]
    have pos3 : 0 < (a * b * c) * (a ^ 2 + b ^ 2 + c ^ 2) := by positivity
    have h5 : 2 * (a ^ 3 + b ^ 3 + c ^ 3) * (a ^ 2 + b ^ 2 + c ^ 2) + 9 * (a + b + c) ^ 2 * (a * b * c) - 33 * (a * b * c) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
                  sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
                  sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
                  sq_nonneg (a + b + c), sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                  mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
                  mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
                  mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith), 
                  lemma_1 a b c ha hb hc
                ]
    have h77 : (2 * (a ^ 3 + b ^ 3 + c ^ 3) * (a ^ 2 + b ^ 2 + c ^ 2) + 9 * (a + b + c) ^ 2 * (a * b * c) - 33 * (a * b * c) * (a ^ 2 + b ^ 2 + c ^ 2) ) / ((a * b * c) * (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith