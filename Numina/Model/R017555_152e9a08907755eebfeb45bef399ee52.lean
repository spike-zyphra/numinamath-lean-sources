import Mathlib

open Real

theorem inequalities_38317 (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (h : a + b = 1) :
    1 / (a / x + b / y) ≤ a * x + b * y := by
  have h1 : 0 < a / x + b / y := by
    positivity
  have h2 : 1 / (a / x + b / y) ≤ a * x + b * y := by
    apply (div_le_iff₀ h1).mpr
    have h4 : (a * x + b * y) * (a / x + b / y) ≥ 1 := by
      have h10 : (a * x + b * y) * (a / x + b / y) = a^2 + b^2 + a * b * (x / y + y / x) := by
        field_simp [show 0 < x by assumption, show 0 < y by assumption]
        ring
      rw [h10]
      have h6 : x / y + y / x ≥ 2 := by
        have h7 : x / y + y / x - 2 ≥ 0 := by
          have h8 : x / y + y / x - 2 = (x - y) ^ 2 / (x * y) := by
            field_simp
            ring
          rw [h8]
          have h9 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
          have h10 : x * y > 0 := mul_pos hx hy
          apply div_nonneg
          exact h9
          linarith
        linarith
      have h8 : a * b > 0 := mul_pos ha hb
      nlinarith [sq_nonneg (a - b), sq_nonneg (x - y), h, mul_pos ha hb, mul_pos ha hx, mul_pos ha hy, mul_pos hb hx, mul_pos hb hy]
    nlinarith
    all_goals nlinarith
  exact h2
  all_goals nlinarith