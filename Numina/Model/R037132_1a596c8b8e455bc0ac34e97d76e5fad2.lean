import Mathlib

theorem algebra_10817 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : a / (b - c) + b / (c - a) + c / (a - b) = 0) :
    a / (b - c)^2 + b / (c - a)^2 + c / (a - b)^2 = 0 := by 
  have ha1 : a - b ≠ 0 := by
    intro h1
    apply ha
    linarith

  have ha2 : a - c ≠ 0 := by
    intro h1
    apply hc
    linarith

  have hb1 : b - a ≠ 0 := by
    intro h1
    apply ha
    linarith

  have hb2 : b - c ≠ 0 := by
    intro h1
    apply hb
    linarith

  have hc1 : c - a ≠ 0 := by
    intro h1
    apply hc
    linarith

  have hc2 : c - b ≠ 0 := by
    intro h1
    apply hb
    linarith

  field_simp [(show b - c ≠ 0 by intro h1; apply hb; linarith),
      (show c - a ≠ 0 by intro h1; apply hc; linarith),
      (show a - b ≠ 0 by intro h1; apply ha; linarith)] at h ⊢
  <;> nlinarith [sq_pos_of_ne_zero (show (b - c) ≠ 0 by intro h1; apply hb; linarith),
      sq_pos_of_ne_zero (show (c - a) ≠ 0 by intro h1; apply hc; linarith),
      sq_pos_of_ne_zero (show (a - b) ≠ 0 by intro h1; apply ha; linarith),
      sq_nonneg (a * (c - a) * (a - b)),
      sq_nonneg (b * (b - c) * (a - b)),
      sq_nonneg (c * (b - c) * (c - a)),
      sq_nonneg ((b - c) * (c - a) * (a - b)), 
      sq_pos_of_ne_zero (show (b - c) * (c - a) * (a - b) ≠ 0 by
        apply mul_ne_zero
        apply mul_ne_zero
        · -- b - c ≠ 0
          intro h1
          apply hb
          linarith
        · -- c - a ≠ 0
          intro h1
          apply hc
          linarith
        · -- a - b ≠ 0
          intro h1
          apply ha
          linarith
      )
  ]