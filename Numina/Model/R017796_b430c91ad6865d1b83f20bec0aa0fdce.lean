import Mathlib

theorem algebra_249949 {a b c : ℝ} (ha : a ≠ -b) (hb : b ≠ -c) (hc : c ≠ -a)
    (h : ∃ d, a^2 + d = b^2 ∧ b^2 + d = c^2) :
    ∃ d, 1 / (b + c) + d = 1 / (c + a) ∧ 1 / (c + a) + d = 1 / (a + b) := by
  rcases h with ⟨d, ⟨ha1, hb1⟩⟩
  have h1 : (b ^ 2 - a ^ 2) = (c ^ 2 - b ^ 2) := by linarith
  use (1 / (c + a) - 1 / (b + c))
  constructor
  · -- Show 1/(b + c) + (1/(c + a) - 1/(b + c)) = 1/(c + a)
    have h3 : c + a ≠ 0 := by
      intro h
      apply hc
      linarith
    have h5 : b + c ≠ 0 := by
      intro h
      apply hb
      linarith
    field_simp [(show b + c ≠ 0 by intro h'; apply hb; linarith),
            (show c + a ≠ 0 by intro h'; apply hc; linarith)]
    <;> nlinarith
  · -- Show 1/(c + a) + (1/(c + a) - 1/(b + c)) = 1/(a + b)
    have h3 : c + a ≠ 0 := by
      intro h
      apply hc
      linarith
    have h4 : a + b ≠ 0 := by
      intro h
      apply ha
      linarith
    have h5 : b + c ≠ 0 := by
      intro h
      apply hb
      linarith
    field_simp [h3, h4, h5]
    <;> nlinarith [sq_pos_of_ne_zero (show c + a ≠ 0 by
        intro h
        apply hc
        linarith
    ), sq_pos_of_ne_zero (show b + c ≠ 0 by
        intro h
        apply hb
        linarith
    ), sq_pos_of_ne_zero (show a + b ≠ 0 by
        intro h
        apply ha
        linarith
    ), sq_pos_of_ne_zero (show c + a ≠ 0 by
        intro h
        apply hc
        linarith
    ), sq_pos_of_ne_zero (show b + c ≠ 0 by
        intro h
        apply hb
        linarith
    ), sq_pos_of_ne_zero (show a + b ≠ 0 by
        intro h
        apply ha
        linarith
    )
    ]