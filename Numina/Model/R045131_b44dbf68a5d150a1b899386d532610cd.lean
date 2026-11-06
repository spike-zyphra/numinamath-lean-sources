import Mathlib

theorem algebra_298063 {x1 x2 a y1 y2 : ℝ} (hx1 : x1 > x2) (hx2 : x2 > 0)
    (ha : 1 > a ∧ a > 0) (hy1 : y1 = x1 / (1 + a) + a * x2 / (1 + a))
    (hy2 : y2 = a * x1 / (1 + a) + x2 / (1 + a)) :
    x1 * x2 < y1 * y2 := by
  rcases ha with ⟨ha1, ha2⟩
  have ha3 : 1 + a > 0 := by
    linarith
  have h1 : y1 * y2 - x1 * x2 > 0 := by
    rw [hy1, hy2]
    have h2 : (x1 / (1 + a) + a * x2 / (1 + a)) * (a * x1 / (1 + a) + x2 / (1 + a)) - x1 * x2 > 0 := by
      have h3 : (x1 / (1 + a) + a * x2 / (1 + a)) * (a * x1 / (1 + a) + x2 / (1 + a)) - x1 * x2 = a * (x1 - x2) ^ 2 / ((1 + a) ^ 2) := by
        field_simp
        ring
      rw [h3]
      have h4 : a * (x1 - x2) ^ 2 / ((1 + a) ^ 2) > 0 := by
        apply div_pos
        have h5 : a * (x1 - x2) ^ 2 > 0 := by
          have hx12 : (x1 - x2) ^ 2 > 0 := by
            have h7 : x1 - x2 > 0 := by linarith
            nlinarith
          nlinarith
        linarith
        all_goals
        have ha3' : (1 + a) ^ 2 > 0 := by
          nlinarith
        nlinarith
      linarith
    linarith
  linarith
  all_goals
  nlinarith