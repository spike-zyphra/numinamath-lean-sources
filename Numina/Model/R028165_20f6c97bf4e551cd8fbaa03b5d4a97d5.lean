import Mathlib

open Real

theorem algebra_599141 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by 
  have h1 : b = 1 - a := by linarith
  rw [h1]
  have h2 : a * (1 - a) > 0 := by
    apply mul_pos
    linarith
    linarith
  have h3 : a > 0 := ha
  have h4 : (1 - a) > 0 := by
    nlinarith
  have h4 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 - 25 / 2 ≥ 0 := by
    have h5 : a * (1 - a) > 0 := h2
    have h5a : a + (1 - a) = 1 := by
      linarith
    have h7 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 - 25 / 2 =
        ( ( (a ^ 2 + 1 ) ^ 2 ) / ( a ^ 2 ) + ( ( ( (1 - a ) ^ 2 + 1 ) ^ 2 ) / ( (1 - a ) ^ 2 ) ) - 25 / 2 ) := by
      field_simp [show a ≠ 0 by linarith, show (1 - a) ≠ 0 by nlinarith]
      <;> ring_nf
    rw [h7]
    have h8 : ( (a ^ 2 + 1 ) ^ 2 ) / (a ^ 2 ) + ( ( ( (1 - a ) ^ 2 + 1 ) ^ 2 ) / ( (1 - a ) ^ 2 ) ) - 25 / 2 ≥ 0 := by
      have h9 : a ^ 2 > 0 := by
        nlinarith
      have h10 : (1 - a) ^ 2 > 0 := by
        nlinarith
      have h11 : ( (a ^ 2 + 1 ) ^ 2 ) / (a ^ 2 ) + ( ( ( (1 - a ) ^ 2 + 1 ) ^ 2 ) / ( (1 - a ) ^ 2 ) ) - 25 / 2 = 
          ( ( (a ^ 2 + 1 ) ^ 2 * (1 - a ) ^ 2 + ( ( (1 - a ) ^ 2 + 1 ) ^ 2 * a ^ 2 ) - ( 25 / 2 ) * ( a ^ 2 * (1 - a ) ^ 2 ) ) / ( a ^ 2 * (1 - a ) ^ 2 ) ) := by 
          field_simp
          <;> ring
      rw [h11]
      have h12 : a ^ 2 * (1 - a) ^ 2 > 0 := by
        positivity
      have h13 : ( (a ^ 2 + 1 ) ^ 2 * (1 - a ) ^ 2 + ( ( (1 - a ) ^ 2 + 1 ) ^ 2 * a ^ 2 ) - ( 25 / 2 ) * ( a ^ 2 * (1 - a ) ^ 2 ) ) ≥ 0 := by
        nlinarith [ sq_nonneg (a - 1 / 2 ), sq_nonneg (a * (a - 1 / 2 )), sq_nonneg ( (a * (1 - a) ) - 1 / 4 ), sq_nonneg ( a - (1 - a ) ), sq_nonneg ( a * (1 - a ) - 1 / 4 ), sq_nonneg ( (a ^ 2 - (1 - a ) ^ 2 ) ), sq_pos_of_pos ( show 0 < a by linarith ), sq_pos_of_pos ( show 0 < (1 - a ) by linarith ), mul_pos ha ( show (0 : ℝ ) < 1 - a by linarith ), mul_pos (show (0 : ℝ ) < a by linarith ) (show (0 : ℝ ) < a by linarith ), mul_pos (show (0 : ℝ ) < 1 - a by linarith ) (show (0 : ℝ ) < 1 - a by linarith )
        ]
      have h14 : ( (a ^ 2 + 1 ) ^ 2 * (1 - a ) ^ 2 + ( ( (1 - a ) ^ 2 + 1 ) ^ 2 * a ^ 2 ) - ( 25 / 2 ) * ( a ^ 2 * (1 - a ) ^ 2 ) ) / ( a ^ 2 * (1 - a ) ^ 2 ) ≥ 0 := by
        apply div_nonneg
        linarith
        linarith
      linarith
    linarith
  linarith