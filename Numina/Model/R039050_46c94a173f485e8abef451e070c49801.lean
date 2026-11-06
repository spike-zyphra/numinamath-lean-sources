import Mathlib

theorem inequalities_2660 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 2 + 7 * a * b + b ^ 2) + 1 / (b ^ 2 + 7 * b * c + c ^ 2) +
    1 / (c ^ 2 + 7 * c * a + a ^ 2) ≥ 1 / (a * b + b * c + c * a) := by

  have h₁ : 0 < a ^ 2 + 7 * a * b + b ^ 2 := by
    nlinarith
  have h₂ : 0 < b ^ 2 + 7 * b * c + c ^ 2 := by
    nlinarith
  have h₃ : 0 < c ^ 2 + 7 * c * a + a ^ 2 := by
    nlinarith
  have h₄ : 0 < a * b + b * c + c * a := by
    positivity

  have h₆ : 1 / (a ^ 2 + 7 * a * b + b ^ 2) + 1 / (b ^ 2 + 7 * b * c + c ^ 2) +
      1 / (c ^ 2 + 7 * c * a + a ^ 2) - 1 / (a * b + b * c + c * a) ≥ 0 := by

    have h₇ : 1 / (a ^ 2 + 7 * a * b + b ^ 2) + 1 / (b ^ 2 + 7 * b * c + c ^ 2) +
        1 / (c ^ 2 + 7 * c * a + a ^ 2) - 1 / (a * b + b * c + c * a) =
        ( (b ^ 2 + 7 * b * c + c ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) * (a * b + b * c + c * a) +
          (a ^ 2 + 7 * a * b + b ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) * (a * b + b * c + c * a) +
          (a ^ 2 + 7 * a * b + b ^ 2) * (b ^ 2 + 7 * b * c + c ^ 2) * (a * b + b * c + c * a) - 
          (a ^ 2 + 7 * a * b + b ^ 2) * (b ^ 2 + 7 * b * c + c ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) ) / ( (a ^ 2 + 7 * a * b + b ^ 2) * (b ^ 2 + 7 * b * c + c ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) * (a * b + b * c + c * a) ) := by
      field_simp
      ring

    rw [h₇]

    have h₈ : (b ^ 2 + 7 * b * c + c ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) * (a * b + b * c + c * a) +
        (a ^ 2 + 7 * a * b + b ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) * (a * b + b * c + c * a) +
        (a ^ 2 + 7 * a * b + b ^ 2) * (b ^ 2 + 7 * b * c + c ^ 2) * (a * b + b * c + c * a) - 
        (a ^ 2 + 7 * a * b + b ^ 2) * (b ^ 2 + 7 * b * c + c ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) ≥ 0 := by
      nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity), 
          mul_pos (show 0 < b * c by positivity) (show 0 < a * b by positivity), 
          mul_pos (show 0 < b * c by positivity) (show 0 < a * c by positivity)
          ]
    have h₉ : ( (b ^ 2 + 7 * b * c + c ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) * (a * b + b * c + c * a) +
        (a ^ 2 + 7 * a * b + b ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) * (a * b + b * c + c * a) +
        (a ^ 2 + 7 * a * b + b ^ 2) * (b ^ 2 + 7 * b * c + c ^ 2) * (a * b + b * c + c * a) - 
        (a ^ 2 + 7 * a * b + b ^ 2) * (b ^ 2 + 7 * b * c + c ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) ) / ( (a ^ 2 + 7 * a * b + b ^ 2) * (b ^ 2 + 7 * b * c + c ^ 2) * (c ^ 2 + 7 * c * a + a ^ 2) * (a * b + b * c + c * a) ) ≥ 0 := by
      apply div_nonneg
      linarith only [h₈]
      positivity
    linarith
  linarith only [h₆]