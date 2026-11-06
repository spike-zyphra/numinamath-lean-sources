import Mathlib

open Real

theorem inequalities_111479 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (P Q R : ℝ)
    (hP : P = sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2)
    (hQ : Q = (a + b) / 2 - sqrt (a * b))
    (hR : R = sqrt (a * b) - 2 * a * b / (a + b)) :
    Q ≥ P ∧ P ≥ R := by

  have h1 : Q ≥ P := by
    rw [hQ, hP]
    have h2 : sqrt ((a ^ 2 + b ^ 2) / 2) + sqrt (a * b) ≤ a + b := by
      have h3 : (sqrt ((a ^ 2 + b ^ 2) / 2) + sqrt (a * b)) ^ 2 ≤ (a + b) ^ 2 := by
        nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sqrt_nonneg (a * b),
          Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]),
          Real.sq_sqrt (show (0 : ℝ) ≤ a * b by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]),
          sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)),
          sq_nonneg (a - b),
          mul_self_nonneg (a - b),
          mul_self_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)),
          Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]),
          Real.sq_sqrt (show (0 : ℝ) ≤ a * b by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb])
          ]
      nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sqrt_nonneg (a * b),
        h3, sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) + sqrt (a * b) - (a + b))
        ]
    nlinarith [h2]

  have h4 : P ≥ R := by
    rw [hP, hR]
    have h5 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ sqrt (a * b) := by
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg (a - b)]
    have h6 : sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2 ≥ sqrt (a * b) - 2 * a * b / (a + b) := by
      have h7 : 0 < a + b := by nlinarith
      have h8 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 := by positivity
      have h9 : sqrt (a * b) ≥ 0 := by positivity

      have h10 : 2 * a * b / (a + b) ≤ (a + b) / 2 := by 
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [sq_nonneg (a - b)]

      have h13 : sqrt ((a ^ 2 + b ^ 2) / 2) * (a + b) - (a + b) ^ 2 / 2 - (sqrt (a * b) * (a + b) - 2 * a * b) ≥ 0 := by
        have h14 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ sqrt (a * b) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg (a - b)]
        have h15 : sqrt ((a ^ 2 + b ^ 2) / 2) * (a + b) - sqrt (a * b) * (a + b) ≥ (a - b) ^ 2 / 2 := by
          nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sqrt_nonneg (a * b),
            Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]),
            Real.sq_sqrt (show (0 : ℝ) ≤ a * b by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]),
            sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)),
            sq_nonneg (a - b)
           ]
        nlinarith

      have h16 : sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2 - (sqrt (a * b) - 2 * a * b / (a + b)) ≥ 0 := by
        have h17 : 0 < a + b := by nlinarith
        have h18 : sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2 - (sqrt (a * b) - 2 * a * b / (a + b)) =
                 (sqrt ((a ^ 2 + b ^ 2) / 2) * (a + b) - (a + b) ^ 2 / 2 - (sqrt (a * b) * (a + b) - 2 * a * b)) / (a + b) := by 
          field_simp
          <;> ring
        rw [h18]
        have h19 : sqrt ((a ^ 2 + b ^ 2) / 2) * (a + b) - (a + b) ^ 2 / 2 - (sqrt (a * b) * (a + b) - 2 * a * b) ≥ 0 := h13
        have h20 : (sqrt ((a ^ 2 + b ^ 2) / 2) * (a + b) - (a + b) ^ 2 / 2 - (sqrt (a * b) * (a + b) - 2 * a * b)) / (a + b) ≥ 0 := by
          apply div_nonneg h19 (by positivity)
        linarith
      linarith
    linarith [h6]

  constructor
  · linarith [h1]
  · linarith [h4]