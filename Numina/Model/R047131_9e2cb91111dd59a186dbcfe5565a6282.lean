import Mathlib


theorem inequalities_605934 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / Real.sqrt ((a + b) * (a + c)) + b / Real.sqrt ((b + a) * (b + c)) + c / Real.sqrt ((c + a) * (c + b)) ≤ 3 / 2 := by

  have h3 : a / Real.sqrt ((a + b) * (a + c)) ≤ (a / (a + b) + a / (a + c)) / 2 := by
    have h4 : 0 < (a + b) * (a + c) := by positivity
    have h5 : 0 < Real.sqrt ((a + b) * (a + c)) := by positivity
    have h7 : a / Real.sqrt ((a + b) * (a + c)) - (a / (a + b) + a / (a + c)) / 2 ≤ 0 := by
      have h121 : a / Real.sqrt ((a + b) * (a + c)) - (a / (a + b) + a / (a + c)) / 2 =
          ( 2 * a * (a + b) * (a + c) - (a * (a + c) + a * (a + b)) * Real.sqrt ((a + b) * (a + c)) ) / ( 2 * Real.sqrt ((a + b) * (a + c)) * (a + b) * (a + c) ) := by
        field_simp [Real.sqrt_pos.mpr (by positivity : 0 < (a + b) * (a + c)), show a + b ≠ 0 by positivity, show a + c ≠ 0 by positivity]
        <;> nlinarith [Real.sqrt_nonneg ((a + b) * (a + c)), Real.sq_sqrt (show 0 ≤ (a + b) * (a + c) by positivity) ]
      rw [h121] at *
      have h1500 : ( 2 * a * (a + b) * (a + c) - (a * (a + c) + a * (a + b)) * Real.sqrt ((a + b) * (a + c)) ) ≤ 0 := by
        have h150 : 2 * a * Real.sqrt ((a + b) * (a + c)) ≤ a * (2*a + b + c) := by
          have h16 : 2 * Real.sqrt ((a + b) * (a + c)) ≤ 2*a + b + c := by
            have h22 : (2 * Real.sqrt ((a + b) * (a + c)) ) ^ 2 ≤ (2*a + b + c) ^ 2 := by
              have h23 : (2 * Real.sqrt ((a + b) * (a + c)) ) ^ 2 = 4 * ((a + b) * (a + c)) := by
                calc
                  (2 * Real.sqrt ((a + b) * (a + c)) ) ^ 2
                    = 4 * (Real.sqrt ((a + b) * (a + c)) ^ 2) := by ring
                  _ = 4 * ((a + b) * (a + c)) := by
                    rw [Real.sq_sqrt]
                    positivity
              nlinarith [show 4 * ((a + b) * (a + c)) ≤ (2*a + b + c) ^ 2 by nlinarith [sq_nonneg (b - c) ] ]
            have h13400 : ( 2 * Real.sqrt ((a + b) * (a + c)) : ℝ ) ≥ 0 := by positivity
            have h13401 : ( 2*a + b + c : ℝ ) ≥ 0 := by positivity
            nlinarith [ Real.sqrt_nonneg ((a + b) * (a + c)) ]
          have h13402 : a > 0 := by linarith
          nlinarith [ Real.sqrt_nonneg ((a + b) * (a + c)) ]
        nlinarith [ Real.sqrt_nonneg ((a + b) * (a + c)), Real.sq_sqrt (show 0 ≤ (a + b) * (a + c) by positivity ) ]
      have h103 : ( 2 * a * (a + b) * (a + c) - (a * (a + c) + a * (a + b)) * Real.sqrt ((a + b) * (a + c)) ) / ( 2 * Real.sqrt ((a + b) * (a + c)) * (a + b) * (a + c) ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        linarith
        positivity
      linarith
    linarith

  have h3a : b / Real.sqrt ((b + a) * (b + c)) ≤ (b / (b + a) + b / (b + c)) / 2 := by
    have h4 : 0 < (b + a) * (b + c) := by positivity
    have h5 : 0 < Real.sqrt ((b + a) * (b + c)) := by positivity
    have h7 : b / Real.sqrt ((b + a) * (b + c)) - (b / (b + a) + b / (b + c)) / 2 ≤ 0 := by
      have h121 : b / Real.sqrt ((b + a) * (b + c)) - (b / (b + a) + b / (b + c)) / 2 =
          ( 2 * b * (b + a) * (b + c) - (b * (b + c) + b * (b + a)) * Real.sqrt ((b + a) * (b + c)) ) / ( 2 * Real.sqrt ((b + a) * (b + c)) * (b + a) * (b + c) ) := by
        field_simp [Real.sqrt_pos.mpr (by positivity : 0 < (b + a) * (b + c)), show b + a ≠ 0 by positivity, show b + c ≠ 0 by positivity]
        <;> nlinarith [Real.sqrt_nonneg ((b + a) * (b + c)), Real.sq_sqrt (show 0 ≤ (b + a) * (b + c) by positivity) ]
      rw [h121] at *
      have h1500 : ( 2 * b * (b + a) * (b + c) - (b * (b + c) + b * (b + a)) * Real.sqrt ((b + a) * (b + c)) ) ≤ 0 := by
        have h150 : 2 * b * Real.sqrt ((b + a) * (b + c)) ≤ b * (2*b + a + c) := by
          have h16 : 2 * Real.sqrt ((b + a) * (b + c)) ≤ 2*b + a + c := by
            have h22 : (2 * Real.sqrt ((b + a) * (b + c)) ) ^ 2 ≤ (2*b + a + c) ^ 2 := by
              have h23 : (2 * Real.sqrt ((b + a) * (b + c)) ) ^ 2 = 4 * ((b + a) * (b + c)) := by
                calc
                  (2 * Real.sqrt ((b + a) * (b + c)) ) ^ 2
                    = 4 * (Real.sqrt ((b + a) * (b + c)) ^ 2) := by ring
                  _ = 4 * ((b + a) * (b + c)) := by
                    rw [Real.sq_sqrt]
                    positivity
              nlinarith [show 4 * ((b + a) * (b + c)) ≤ (2*b + a + c) ^ 2 by nlinarith [sq_nonneg (a - c) ] ]
            have h13400 : ( 2 * Real.sqrt ((b + a) * (b + c)) : ℝ ) ≥ 0 := by positivity
            have h13401 : ( 2*b + a + c : ℝ ) ≥ 0 := by positivity
            nlinarith [ Real.sqrt_nonneg ((b + a) * (b + c)) ]
          have h13402 : b > 0 := by linarith
          nlinarith [ Real.sqrt_nonneg ((b + a) * (b + c)) ]
        nlinarith [ Real.sqrt_nonneg ((b + a) * (b + c)), Real.sq_sqrt (show 0 ≤ (b + a) * (b + c) by positivity ) ]
      have h103 : ( 2 * b * (b + a) * (b + c) - (b * (b + c) + b * (b + a)) * Real.sqrt ((b + a) * (b + c)) ) / ( 2 * Real.sqrt ((b + a) * (b + c)) * (b + a) * (b + c) ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        linarith
        positivity
      linarith
    linarith

  have h3b : c / Real.sqrt ((c + a) * (c + b)) ≤ (c / (c + a) + c / (c + b)) / 2 := by
    have h4 : 0 < (c + a) * (c + b) := by positivity
    have h5 : 0 < Real.sqrt ((c + a) * (c + b)) := by positivity
    have h7 : c / Real.sqrt ((c + a) * (c + b)) - (c / (c + a) + c / (c + b)) / 2 ≤ 0 := by
      have h121 : c / Real.sqrt ((c + a) * (c + b)) - (c / (c + a) + c / (c + b)) / 2 =
          ( 2 * c * (c + a) * (c + b) - (c * (c + b) + c * (c + a)) * Real.sqrt ((c + a) * (c + b)) ) / ( 2 * Real.sqrt ((c + a) * (c + b)) * (c + a) * (c + b) ) := by
        field_simp [Real.sqrt_pos.mpr (by positivity : 0 < (c + a) * (c + b)), show c + a ≠ 0 by positivity, show c + b ≠ 0 by positivity]
        <;> nlinarith [Real.sqrt_nonneg ((c + a) * (c + b)), Real.sq_sqrt (show 0 ≤ (c + a) * (c + b) by positivity) ]
      rw [h121] at *
      have h1500 : ( 2 * c * (c + a) * (c + b) - (c * (c + b) + c * (c + a)) * Real.sqrt ((c + a) * (c + b)) ) ≤ 0 := by
        have h150 : 2 * c * Real.sqrt ((c + a) * (c + b)) ≤ c * (2*c + a + b) := by
          have h16 : 2 * Real.sqrt ((c + a) * (c + b)) ≤ 2*c + a + b := by
            have h22 : (2 * Real.sqrt ((c + a) * (c + b)) ) ^ 2 ≤ (2*c + a + b) ^ 2 := by
              have h23 : (2 * Real.sqrt ((c + a) * (c + b)) ) ^ 2 = 4 * ((c + a) * (c + b)) := by
                calc
                  (2 * Real.sqrt ((c + a) * (c + b)) ) ^ 2
                    = 4 * (Real.sqrt ((c + a) * (c + b)) ^ 2) := by ring
                  _ = 4 * ((c + a) * (c + b)) := by
                    rw [Real.sq_sqrt]
                    positivity
              nlinarith [show 4 * ((c + a) * (c + b)) ≤ (2*c + a + b) ^ 2 by nlinarith [sq_nonneg (a - b) ] ]
            have h13400 : ( 2 * Real.sqrt ((c + a) * (c + b)) : ℝ ) ≥ 0 := by positivity
            have h13401 : ( 2*c + a + b : ℝ ) ≥ 0 := by positivity
            nlinarith [ Real.sqrt_nonneg ((c + a) * (c + b)) ]
          have h13402 : c > 0 := by linarith
          nlinarith [ Real.sqrt_nonneg ((c + a) * (c + b)) ]
        nlinarith [ Real.sqrt_nonneg ((c + a) * (c + b)), Real.sq_sqrt (show 0 ≤ (c + a) * (c + b) by positivity ) ]
      have h103 : ( 2 * c * (c + a) * (c + b) - (c * (c + b) + c * (c + a)) * Real.sqrt ((c + a) * (c + b)) ) / ( 2 * Real.sqrt ((c + a) * (c + b)) * (c + a) * (c + b) ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        linarith
        positivity
      linarith
    linarith

  have h4 : a / Real.sqrt ((a + b) * (a + c)) + b / Real.sqrt ((b + a) * (b + c)) + c / Real.sqrt ((c + a) * (c + b)) ≤ (a / (a + b) + a / (a + c) + b / (b + a) + b / (b + c) + c / (c + a) + c / (c + b)) / 2 := by
    linarith [h3, h3a, h3b]

  have h5 : (a / (a + b) + a / (a + c) + b / (b + a) + b / (b + c) + c / (c + a) + c / (c + b)) / 2 = 3 / 2 := by
    field_simp
    <;> nlinarith

  linarith [h4, h5]