import Mathlib

theorem inequalities_108787 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) ≤ 1 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : a * b * c = 1 := habc
  have h3 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 ≤ 0 := by
    have h4 : 0 < a ^ 2 + 2 := by
      nlinarith [sq_pos_of_pos ha]
    have h5 : 0 < b ^ 2 + 2 := by
      nlinarith [sq_pos_of_pos hb]
    have h6 : 0 < c ^ 2 + 2 := by
      nlinarith [sq_pos_of_pos hc]
    have h7 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 ≤ 0 := by
      have h8 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 =
          (a * (b ^ 2 + 2) * (c ^ 2 + 2) + b * (a ^ 2 + 2) * (c ^ 2 + 2) + c * (a ^ 2 + 2) * (b ^ 2 + 2) - (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2)) / ((a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2)) := by
        field_simp
        <;> ring
      rw [h8] at *
      have h9 : a * (b ^ 2 + 2) * (c ^ 2 + 2) + b * (a ^ 2 + 2) * (c ^ 2 + 2) + c * (a ^ 2 + 2) * (b ^ 2 + 2) - (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2) ≤ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h10 : (a * (b ^ 2 + 2) * (c ^ 2 + 2) + b * (a ^ 2 + 2) * (c ^ 2 + 2) + c * (a ^ 2 + 2) * (b ^ 2 + 2) - (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2)) / ((a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2)) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        linarith
        all_goals
          positivity
      linarith
    linarith
  linarith