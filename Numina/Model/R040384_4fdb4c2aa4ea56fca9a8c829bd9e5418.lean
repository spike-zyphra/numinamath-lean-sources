import Mathlib

theorem inequalities_159337 (a b c : ℝ) (h : a + b + c = 3) :
    1 / (5 * a ^ 2 - 4 * a + 11) + 1 / (5 * b ^ 2 - 4 * b + 11) +
    1 / (5 * c ^ 2 - 4 * c + 11) ≤ 1 / 4 := by

  have h1 : c = 3 - a - b := by linarith
  have h2 : 0 < (5 * a ^ 2 - 4 * a + 11 : ℝ) := by
    nlinarith [sq_nonneg (a - 2 / 5)]
  have h3 : 0 < (5 * b ^ 2 - 4 * b + 11 : ℝ) := by
    nlinarith [sq_nonneg (b - 2 / 5)]
  have h4 : 0 < (5 * c ^ 2 - 4 * c + 11 : ℝ) := by
    rw [h1]
    nlinarith [sq_nonneg ( (3 - a - b : ℝ) - 2 / 5 ), sq_nonneg (a + b - 3 : ℝ) ]

  have h5 : 1 / (5 * a ^ 2 - 4 * a + 11) + 1 / (5 * b ^ 2 - 4 * b + 11) + 1 / (5 * c ^ 2 - 4 * c + 11) - 1 / 4 ≤ 0 := by 
    have h14 : c = 3 - a - b := h1
    rw [h14]
    have h15 : 0 < (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11 : ℝ) := by
      nlinarith [sq_nonneg ( (3 - a - b : ℝ) - 2 / 5 ), sq_nonneg (a + b - 3 : ℝ) ]
    have h17 : (1 / (5 * a ^ 2 - 4 * a + 11) + 1 / (5 * b ^ 2 - 4 * b + 11) + 1 / (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) - 1 / 4 ≤ 0) := by
      have h18 : 0 < (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) := by
        positivity
      have h19 : (1 / (5 * a ^ 2 - 4 * a + 11) + 1 / (5 * b ^ 2 - 4 * b + 11) + 1 / (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) - 1 / 4) =
          ( ( (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) * 4 + (5 * a ^ 2 - 4 * a + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) * 4 + (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * 4 - (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) ) / (4 * (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) ) ) := by 
        field_simp
        <;> ring
      rw [h19] 
      have h20 : 4 * (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) > 0 := by
        positivity
      have h21 : ( (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) * 4 + (5 * a ^ 2 - 4 * a + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) * 4 + (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * 4 - (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) ) ≤ 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - (3 - a - b)), sq_nonneg (b - (3 - a - b)), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((3 - a - b) - 1),
          sq_nonneg (a + b - (3 - a - b)), 
          mul_nonneg (sq_nonneg (a - 1)) (sq_nonneg (b - 1)), 
          mul_nonneg (sq_nonneg (a - 1)) (sq_nonneg ((3 - a - b) - 1)), 
          mul_nonneg (sq_nonneg (b - 1)) (sq_nonneg ((3 - a - b) - 1)), 
          sq_nonneg ( (a) * (b) - 1 ), sq_nonneg ( (a) * (3 - a - b) - 1 ) , sq_nonneg ( (b) * (3 - a - b) - 1) ]
      have h22 : ( (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) * 4 + (5 * a ^ 2 - 4 * a + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) * 4 + (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * 4 - (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) ) / (4 * (5 * a ^ 2 - 4 * a + 11) * (5 * b ^ 2 - 4 * b + 11) * (5 * (3 - a - b) ^ 2 - 4 * (3 - a - b) + 11) ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg h21 (by positivity)
      linarith
    linarith

  linarith