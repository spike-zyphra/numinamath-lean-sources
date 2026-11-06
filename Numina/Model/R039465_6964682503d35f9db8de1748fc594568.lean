import Mathlib

theorem number_theory_82097 (a b c : ℚ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    IsSquare ((1 / (b - c)^2) + (1 / (c - a)^2) + (1 / (a - b)^2)) := by 
  use (1 / (b - c) + 1 / (c - a) + 1 / (a - b))
  field_simp [(show b - c ≠ 0 by
    intro h
    apply hbc
    linarith
    ), (show c - a ≠ 0 by
    intro h
    apply hca
    linarith
    ), (show a - b ≠ 0 by
    intro h
    apply hab
    linarith
    ), (show (b - c) ≠ 0 by
    intro h
    apply hbc
    linarith
    ), (show (c - a) ≠ 0 by
    intro h
    apply hca
    linarith
    ), (show (a - b) ≠ 0 by
    intro h
    apply hab
    linarith
    ) ]
  <;> ring