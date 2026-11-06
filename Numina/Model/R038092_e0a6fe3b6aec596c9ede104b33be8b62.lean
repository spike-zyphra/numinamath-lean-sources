import Mathlib

theorem inequalities_137874 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥
    Real.sqrt 3 + a * b / (a + b) + b * c / (b + c) + c * a / (c + a) := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + a := by linarith
  have h4 : (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) - (Real.sqrt 3 + a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≥ 0 := by
    have h12 : (1 / (a + b) + 1 / (b + c) + 1 / (c + a) ) - (Real.sqrt 3 + a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) =
        ((1 - a * b) / (a + b) + (1 - b * c) / (b + c) + (1 - c * a) / (c + a) - Real.sqrt 3) := by
      field_simp
      ring
    rw [h12]
    have h13 : (1 - a * b) / (a + b) + (1 - b * c) / (b + c) + (1 - c * a) / (c + a) = a + b + c := by
      have h7 : 1 - a * b = b * c + c * a := by
        nlinarith
      have h8 : 1 - b * c = a * b + c * a := by
        nlinarith
      have h9 : 1 - c * a = a * b + b * c := by
        nlinarith
      have h10 : (1 - a * b) / (a + b) = c := by
        rw [h7]
        field_simp
        all_goals nlinarith
      have h11 : (1 - b * c) / (b + c) = a := by
        rw [h8]
        field_simp
        all_goals nlinarith
      have h12 : (1 - c * a) / (c + a) = b := by
        rw [h9]
        field_simp
        all_goals nlinarith
      linarith [h10, h11, h12]
    rw [h13]
    have h14 : a + b + c ≥ Real.sqrt 3 := by
      have h15 : (a + b + c) ^ 2 ≥ 3 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have h17 : a + b + c ≥ 0 := by positivity
      have h18 : Real.sqrt ((a + b + c) ^ 2) ≥ Real.sqrt (3 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h19 : Real.sqrt ((a + b + c) ^ 2) = a + b + c := by
        rw [Real.sqrt_sq (show 0 ≤ a + b + c by positivity)]
      have h20 : Real.sqrt (3 : ℝ) = Real.sqrt 3 := by rfl
      nlinarith
    linarith
  linarith