import Mathlib

theorem inequalities_600877 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ((a^2 - b^2)^3 + (b^2 - c^2)^3 + (c^2 - a^2)^3) /
    ((a - b)^3 + (b - c)^3 + (c - a)^3) > 8 * a * b * c := by

  have h1 : a - b ≠ 0 := by
    intro h
    apply hne.1
    linarith
  have h2 : a - c ≠ 0 := by
    intro h
    apply hne.2.1
    linarith
  have h3 : b - c ≠ 0 := by
    intro h
    apply hne.2.2
    linarith
  have h4 : (a^2 - b^2)^3 + (b^2 - c^2)^3 + (c^2 - a^2)^3 =
      3 * ((a^2 - b^2) * (b^2 - c^2) * (c^2 - a^2)) := by
    ring
  have h5 : (a - b)^3 + (b - c)^3 + (c - a)^3 =
      3 * ((a - b) * (b - c) * (c - a)) := by
    ring
  have h6 : ((a^2 - b^2)^3 + (b^2 - c^2)^3 + (c^2 - a^2)^3) /
      ((a - b)^3 + (b - c)^3 + (c - a)^3) = (a + b) * (b + c) * (c + a) := by
    rw [h4, h5]
    field_simp [(show (a - b : ℝ) ≠ 0 by exact h1), (show (b - c : ℝ) ≠ 0 by exact h3), (show (c - a : ℝ) ≠ 0 by
      intro h
      apply h2
      linarith
    ), (show (a - b : ℝ) ≠ 0 by exact h1), (show (b - c : ℝ) ≠ 0 by exact h3)]
    ring
  rw [h6]
  have h7 : (a + b) * (b + c) * (c + a) > 8 * a * b * c := by
    have h8 : (a + b) * (b + c) * (c + a) - 8 * a * b * c > 0 := by
      have h10 : (a + b) * (b + c) * (c + a) - 8 * a * b * c = a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) - 6 * a * b * c := by
        ring
      rw [h10]
      have h11 : a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) > 6 * a * b * c := by
        nlinarith [sq_pos_of_ne_zero (show (a - b : ℝ) ≠ 0 by
          intro h
          apply hne.1
          linarith
        ), sq_pos_of_ne_zero (show (a - c : ℝ) ≠ 0 by
          intro h
          apply hne.2.1
          linarith
        ), sq_pos_of_ne_zero (show (b - c : ℝ) ≠ 0 by
          intro h
          apply hne.2.2
          linarith
        ), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      linarith
    linarith
  linarith