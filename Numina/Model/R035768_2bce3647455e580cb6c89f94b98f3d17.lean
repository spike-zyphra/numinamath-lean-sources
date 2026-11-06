import Mathlib

theorem algebra_229626 {a b c : ℝ} (ha : a ≠ -b) (hb : b ≠ -c) (hc : c ≠ -a) :
    (a^2 - b^2) / (a + b)^2 + (b^2 - c^2) / (b + c)^2 + (c^2 - a^2) / (c + a)^2 =
    (a - b) * (b - c) * (a - c) / ((a + b) * (b + c) * (c + a)) := by
  have ha1 : a + b ≠ 0 := by
    intro h
    apply ha
    linarith
  have hb1 : b + c ≠ 0 := by
    intro h
    apply hb
    linarith
  have hc1 : c + a ≠ 0 := by
    intro h
    apply hc
    linarith
  field_simp [(show a + b ≠ 0 by
    intro h
    apply ha1
    linarith
  ), (show b + c ≠ 0 by
    intro h
    apply hb1
    linarith
  ), (show c + a ≠ 0 by
    intro h
    apply hc1
    linarith
  ), (show (a + b) * (b + c) * (c + a) ≠ 0 by
    apply mul_ne_zero
    apply mul_ne_zero
    exact ha1
    exact hb1
    exact hc1
  ), pow_two (a + b), pow_two (b + c), pow_two (c + a)]
  <;> ring_nf
  <;> field_simp [(show a + b ≠ 0 by
      intro h
      apply ha1
      linarith
    ), (show b + c ≠ 0 by
      intro h
      apply hb1
      linarith
    ), (show c + a ≠ 0 by
      intro h
      apply hc1
      linarith
    ), (show (a + b) * (b + c) * (c + a) ≠ 0 by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha1
      exact hb1
      exact hc1
    ), pow_two (a + b), pow_two (b + c), pow_two (c + a)]
  <;> ring