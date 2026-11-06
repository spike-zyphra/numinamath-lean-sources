import Mathlib

theorem algebra_287197 {a b x : ℝ} (hb : b ≠ 0) 
    (hab : a^2 ≠ b^2) (hx : x = (a^2 - b^2) / (2 * b)) :
    a / x + Real.sqrt ((a^2) / (x^2) + 1) = 
    if a^2 > b^2 then (a + b) / (a - b) else (b - a) / (a + b) := by

  have h1 : x = (a ^ 2 - b ^ 2) / (2 * b) := hx
  have h2 : a^2 - b^2 ≠ 0 := by
    intro h
    apply hab
    linarith

  have h3 : a / x = 2 * a * b / (a ^ 2 - b ^ 2) := by
    rw [h1]
    field_simp [(show (2 * b) ≠ 0 by
      intro h'
      apply hb
      linarith
    ), (show a ^ 2 - b ^ 2 ≠ 0 by
      intro h'
      apply hab
      linarith
    )
    ]
    <;> ring

  have h4 : (a ^ 2) / (x ^ 2) + 1 = ((a ^ 2 + b ^ 2) ^ 2) / ((a ^ 2 - b ^ 2) ^ 2) := by
    rw [h1]
    field_simp [(show (2 * b) ≠ 0 by
      intro h'
      apply hb
      linarith
    ), (show (a ^ 2 - b ^ 2) ≠ 0 by
      intro h'
      apply hab
      linarith
    )
    ]
    ring_nf

  have h5 : Real.sqrt ((a ^ 2) / (x ^ 2) + 1) = (a ^ 2 + b ^ 2) / |a ^ 2 - b ^ 2| := by
    rw [h4]
    have h6 : Real.sqrt (((a ^ 2 + b ^ 2) ^ 2) / ((a ^ 2 - b ^ 2) ^ 2)) =
        Real.sqrt ((a ^ 2 + b ^ 2) ^ 2) / Real.sqrt ((a ^ 2 - b ^ 2) ^ 2) := by
      rw [Real.sqrt_div (by
        have h17 : (a^2 + b^2) ^ 2 ≥ 0 := by positivity
        have h18 : (a^2 - b^2) ^ 2 ≥ 0 := by positivity
        positivity
      )
      ]
    rw [h6]
    have h7 : Real.sqrt ((a ^ 2 + b ^ 2) ^ 2) = a ^ 2 + b ^ 2 := by
      rw [Real.sqrt_sq (show 0 ≤ a ^ 2 + b ^ 2 by positivity)]
    have h8 : Real.sqrt ((a ^ 2 - b ^ 2) ^ 2) = |a ^ 2 - b ^ 2| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h7, h8]

  rw [h3, h5]

  by_cases h : a ^ 2 > b ^ 2
  · -- if a^2 > b^2
    have h13 : |a ^ 2 - b ^ 2| = a ^ 2 - b ^ 2 := by
      apply abs_of_pos
      nlinarith
    rw [h13]
    rw [if_pos h]
    have h14 : 2 * a * b / (a ^ 2 - b ^ 2) + (a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) = (a + b) / (a - b) := by
      have h17 : a ^ 2 - b ^ 2 ≠ 0 := by
        intro h'
        apply hab
        linarith
      field_simp [(show a ^ 2 - b ^ 2 ≠ 0 by exact h17), (show a - b ≠ 0 by
        by_contra h0
        have : a = b := by linarith
        have h17 : a ^ 2 = b ^ 2 := by
          rw [show a = b by linarith]
        tauto
      ), (show (a + b) ≠ 0 by
        by_contra h0
        have : a = -b := by linarith
        have h17 : a ^ 2 = b ^ 2 := by
          rw [show a = -b by linarith]
          ring
        tauto
      )
      ]
      <;> nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
        by_contra h0
        have : a = b := by linarith
        have h17 : a ^ 2 = b ^ 2 := by
          rw [show a = b by linarith]
        tauto
      ), sq_pos_of_ne_zero (show (a + b) ≠ 0 by
        by_contra h0
        have : a = -b := by linarith
        have h17 : a ^ 2 = b ^ 2 := by
          rw [show a = -b by linarith]
          ring
        tauto
      )
      ]
    linarith
  · -- else
    have h15 : a ^ 2 ≤ b ^ 2 := by nlinarith
    have h13 : |a ^ 2 - b ^ 2| = b ^ 2 - a ^ 2 := by
      have h16 : a ^ 2 - b ^ 2 ≤ 0 := by nlinarith
      rw [abs_of_nonpos h16]
      all_goals nlinarith
    rw [h13]
    rw [if_neg (show ¬ a ^ 2 > b ^ 2 by linarith)]
    have h14 : 2 * a * b / (a ^ 2 - b ^ 2) + (a ^ 2 + b ^ 2) / (b ^ 2 - a ^ 2) = (b - a) / (a + b) := by
      have h17 : a ^ 2 - b ^ 2 ≠ 0 := by
        intro h'
        apply hab
        linarith
      have h18 : b ^ 2 - a ^ 2 ≠ 0 := by
        intro h0
        have h17 : a ^ 2 - b ^ 2 = 0 := by linarith
        have h8 : a ^ 2 - b ^ 2 = 0 := by linarith
        have : a ^ 2 = b ^ 2 := by linarith
        tauto
      field_simp [(show a ^ 2 - b ^ 2 ≠ 0 by exact h17), (show b ^ 2 - a ^ 2 ≠ 0 by exact h18), (show a + b ≠ 0 by
        by_contra h0
        have : a = -b := by linarith
        have h17 : a ^ 2 = b ^ 2 := by
          rw [show a = -b by linarith]
          ring
        tauto
      )
      ]
      <;> nlinarith [sq_pos_of_ne_zero (show (a + b) ≠ 0 by
        by_contra h0
        have : a = -b := by linarith
        have h17 : a ^ 2 = b ^ 2 := by
          rw [show a = -b by linarith]
          ring
        tauto
      ), sq_nonneg (a ^ 2 - b ^ 2)
      ]
    linarith