import Mathlib

theorem inequalities_601437 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 / ((2 * a + b) * (2 * a + c)) +
    b^2 / ((2 * b + c) * (2 * b + a)) +
    c^2 / ((2 * c + a) * (2 * c + b)) ≤ 1 / 3 := by

  have ha1 : 0 < 2 * a + b := by linarith [ha, hb]
  have ha2 : 0 < 2 * a + c := by linarith [ha, hc];
  have hb1 : 0 < 2 * b + c := by linarith [hb, hc];
  have hb2 : 0 < 2 * b + a := by linarith [hb, ha];
  have hc1 : 0 < 2 * c + a := by linarith [hc, ha];
  have hc2 : 0 < 2 * c + b := by linarith [hc, hb];
  
  have h1 : a^2 / ((2 * a + b) * (2 * a + c)) +
    b^2 / ((2 * b + c) * (2 * b + a)) +
    c^2 / ((2 * c + a) * (2 * c + b)) - 1 / 3 ≤ 0 := by
    have h2 : a^2 / ((2 * a + b) * (2 * a + c)) +
      b^2 / ((2 * b + c) * (2 * b + a)) + c^2 / ((2 * c + a) * (2 * c + b)) - 1 / 3 =
      (a^2 * (2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b) +
      b^2 * (2 * a + c) * (2 * a + b) * (2 * c + a) * (2 * c + b) +
      c^2 * (2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a) - 1 / 3 * ((2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b))
     ) / ((2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b)) := by
      field_simp
      ring
    rw [h2]
    have h8 : ((2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b)) > 0 := by positivity
    have h2 : a^2 * (2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b) +
      b^2 * (2 * a + c) * (2 * a + b) * (2 * c + a) * (2 * c + b) +
      c^2 * (2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a) - 1 / 3 * ((2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b)) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]

    apply div_nonpos_of_nonpos_of_nonneg h2 (show ((2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b)) ≥ 0 by positivity)

  linarith [show
    a^2 / ((2 * a + b) * (2 * a + c)) + b^2 / ((2 * b + c) * (2 * b + a)) + c^2 / ((2 * c + a) * (2 * c + b)) - 1 / 3 ≤ 0
    from by linarith [h1]]