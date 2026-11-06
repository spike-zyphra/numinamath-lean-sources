import Mathlib

open Real

theorem inequalities_310498 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    2 * sqrt 3 ≤ (1 - a * b - b * c - c * a) / sqrt (a * b * c) := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : sqrt (a * b * c) > 0 := by
    apply Real.sqrt_pos.mpr
    positivity

  have h6 : (1 - a * b - b * c - c * a) / sqrt (a * b * c) ≥ 2 * sqrt 3 := by
    have h7 : sqrt (a * b * c) > 0 := h2
    have h8 : (1 - a * b - b * c - c * a) ≥ 2 * sqrt 3 * sqrt (a * b * c) := by
      have h11 : (1 - a * b - b * c - c * a) ^ 2 ≥ (2 * sqrt 3 * sqrt (a * b * c)) ^ 2 := by
        have h12 : (2 * sqrt 3 * sqrt (a * b * c)) ^ 2 = 12 * (a * b * c) := by
          calc
            (2 * sqrt 3 * sqrt (a * b * c)) ^ 2 = 4 * (sqrt 3 ^ 2) * (sqrt (a * b * c) ^ 2) := by ring
            _ = 4 * 3 * (a * b * c) := by
              have h14 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
              have h15 : sqrt (a * b * c) ^ 2 = a * b * c := by
                rw [Real.sq_sqrt]
                positivity
              rw [h14, h15]
            _ = 12 * (a * b * c) := by ring

        have h13 : (1 - a * b - b * c - c * a) ^ 2 ≥ 12 * (a * b * c) := by
          have h4 : c = 1 - a - b := by linarith
          rw [h4]
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
                      mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by nlinarith), mul_pos hb (show 0 < 1 - a - b by nlinarith), 
                      sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - (1 - a - b) * a), sq_nonneg ((1 - a - b) * a - a * b)

          ]
        nlinarith [h12, h13, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h14 : (1 - a * b - b * c - c * a) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          h
        ]
      have h15 : 2 * sqrt 3 * sqrt (a * b * c) ≥ 0 := by
        positivity
      nlinarith [show (0 : ℝ) ≤ 1 - a * b - b * c - c * a by linarith, 
        show (0 : ℝ) ≤ 2 * sqrt 3 * sqrt (a * b * c) by positivity, 
        sq_nonneg ( (1 - a * b - b * c - c * a) - (2 * sqrt 3 * sqrt (a * b * c)) )
      ]
    have h9 : (1 - a * b - b * c - c * a) / sqrt (a * b * c) ≥ 2 * sqrt 3 := by
      have h7' : sqrt (a * b * c) > 0 := h2
      apply (le_div_iff₀ h7').mpr
      linarith [h8]
    exact h9

  exact h6