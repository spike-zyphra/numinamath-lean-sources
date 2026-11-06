import Mathlib

open Real
open scoped BigOperators

theorem inequalities_192282 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hA hB hC : ℝ) (hA' : hA = (a + b) / 2) (hB' : hB = (b + c) / 2) (hC' : hC = (c + a) / 2) :
  hA * hB * hC ≥ (1 / 8) * (a + b) * (b + c) * (c + a) := by
  rw [hA', hB', hC']
  have h1 : ((a + b) / 2) * ((b + c) / 2) * ((c + a) / 2) ≥ (1 / 8) * (a + b) * (b + c) * (c + a) := by
    have h2 : ((a + b) / 2) * ((b + c) / 2) * ((c + a) / 2) = ( (a + b) * (b + c) * (c + a) ) / 8 := by
      ring_nf
    rw [h2]
    have h3 : ( (a + b) * (b + c) * (c + a) ) / 8 ≥ (1 / 8) * (a + b) * (b + c) * (c + a) := by
      have h5 : ( (a + b) * (b + c) * (c + a) ) / 8 - (1 / 8) * (a + b) * (b + c) * (c + a) ≥ 0 := by
        have h6 : ( (a + b) * (b + c) * (c + a) ) / 8 - (1 / 8) * (a + b) * (b + c) * (c + a) =
          ( (a + b) * (b + c) * (c + a) - (a + b) * (b + c) * (c + a) ) / 8 := by
          ring_nf
        rw [h6]
        have h7 : ( (a + b) * (b + c) * (c + a) - (a + b) * (b + c) * (c + a) ) = 0 := by
          ring_nf
        rw [h7]
        norm_num
      linarith
    linarith
  linarith