import Mathlib

theorem inequalities_110295 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) ≥ 1 := by
  have h1 : b = 2 - a := by linarith
  rw [h1] at *
  have h2 : 0 < 2 - a := by nlinarith
  have h3 : 0 < a := ha
  have h4 : a < 2 := by nlinarith
  have h5 : 1 / (a ^ 2 + 1) + 1 / ((2 - a) ^ 2 + 1) - 1 ≥ 0 := by
    have h6 : 1 / (a ^ 2 + 1) + 1 / ((2 - a) ^ 2 + 1) - 1 =
        ( (2 - a ) ^ 2 + 1 + a ^ 2 + 1 - (a ^ 2 + 1 ) * ( (2 - a ) ^ 2 + 1 ) ) / ( (a ^ 2 + 1 ) * ( (2 - a ) ^ 2 + 1 ) ) := by
      field_simp
      <;> ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - 1), sq_nonneg ( (2 - a) - 1 ), 
      sq_nonneg ( a - (2 - a) ), sq_nonneg ( a * (2 - a) - 1 ), 
      sq_nonneg (a^2 - (2 - a)^2 ), mul_pos (show 0 < a by linarith) (show 0 < (2 - a) by nlinarith)
    ]
    all_goals positivity
  linarith