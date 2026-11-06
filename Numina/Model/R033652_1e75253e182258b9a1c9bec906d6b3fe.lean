import Mathlib

theorem inequalities_25678 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdist : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    ((a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3) /
    ((a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3) > 8 * a * b * c := by

  have h8 : (a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3 =
      3 * ((a^2 - b^2) * (b^2 - c^2) * (c^2 - a^2)) := by
    ring_nf

  have h9 : (a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3 = 3 * ((a - b) * (b - c) * (c - a)) := by
    ring_nf

  have h10 : ((a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3) / ((a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3) = (a + b) * (b + c) * (c + a) := by 
    rw [h8, h9]
    field_simp [(show (a - b) ≠ 0 by 
      intro h'
      apply hdist.1
      linarith
    ), (show (b - c) ≠ 0 by 
      intro h'
      apply hdist.2.1
      linarith
    ), (show (c - a) ≠ 0 by 
      intro h'
      apply hdist.2.2 
      linarith 
    )]
    ring_nf

  have h13 : ((a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3) / ((a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3) > 8 * a * b * c := by
    rw [h10]
    have hx1 : (a + b) * (b + c) * (c + a) > 8 * a * b * c := by
      have h11 : 0 < a := ha
      have h12 : 0 < b := hb
      have h13 : 0 < c := hc
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        sq_pos_of_ne_zero (show (a - b) ≠ 0 by
          intro h
          apply hdist.1
          linarith
        ), sq_pos_of_ne_zero (show (b - c) ≠ 0 by
          intro h 
          apply hdist.2.1 
          linarith 
        ), sq_pos_of_ne_zero (show (c - a) ≠ 0 by 
          intro h 
          apply hdist.2.2 
          linarith 
        )
      ]
    linarith [hx1]

  exact h13