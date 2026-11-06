import Mathlib

open Real

theorem inequalities_305407 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    9 / 4 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ∧
    1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≤ 5 / 2 := by

  have h1 : 0 ≤ c := hc
  have h2 : 0 < 1 + a := by linarith
  have h3 : 0 < 1 + b := by linarith
  have h4 : 0 < 1 + c := by linarith

  have h5 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 9 / 4 ≥ 0 := by
    have h5a : 0 < (1 + a) * (1 + b) * (1 + c) := by
      positivity

    have eq1 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 9 / 4 =
        ( (1 + b) * (1 + c) * 4 + (1 + a) * (1 + c) * 4 + (1 + a) * (1 + b) * 4 - 9 * (1 + a) * (1 + b) * (1 + c) ) / (4 * (1 + a) * (1 + b) * (1 + c) ) := by 
      field_simp 
      ring

    rw [eq1] 
    apply div_nonneg
    · -- To show the numerator ≥ 0
      have h6 : c = 1 - a - b := by 
        linarith 
      rw [h6]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - a - b by nlinarith) ha 
        ]
    · -- Show the denominator is positive 
      positivity

  have h5' : 9 / 4 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) := by 
    linarith [h5]

  have h7 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 5 / 2 ≤ 0 := by 
    have h5a : 0 < (1 + a) * (1 + b) * (1 + c) := by 
      positivity 
    have eq2 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 5 / 2 =
      ( (1 + b) * (1 + c) * 2 + (1 + a) * (1 + c) * 2 + (1 + a) * (1 + b) * 2 - 5 * (1 + a) * (1 + b) * (1 + c) ) / (2 * (1 + a) * (1 + b) * (1 + c) ) := by 
      field_simp 
      ring
    rw [eq2] 
    apply div_nonpos_of_nonpos_of_nonneg 
    · -- To show the numerator ≤ 0 
      have h6 : c = 1 - a - b := by 
        linarith 
      rw [h6] 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - a - b by nlinarith) ha 
        ]
    · -- Show the denominator is positive 
      positivity 
  have h7' : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≤ 5 / 2 := by 
    linarith [h7]

  exact ⟨h5', h7'⟩