import Mathlib

theorem algebra_9090_1 : ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 9 ∧ 2 / a + 2 / b + 2 / c = 2 := by
  -- Note that I break the problem into two:
  -- 1. There exists a, b, c such that a + b + c = 9 and 2 / a + 2 / b + 2 / c = 2
  -- 2. For any a, b, c such that a + b + c = 9, 2 / a + 2 / b + 2 / c ≥ 2
  -- The first part is trivial by setting a = b = c = 3
  use 3, 3, 3
  norm_num

theorem algebra_9090_2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 9) :
    2 / a + 2 / b + 2 / c ≥ 2 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : 2 / a + 2 / b + 2 / c - 2 ≥ 0 := by
    have h3 : 2 / a + 2 / b + 2 / c - 2 =
        ( 2 * (b * c + a * c + a * b) - 2 * (a * b * c) ) / (a * b * c) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    have h4 : 2 * (b * c + a * c + a * b) ≥ 2 * (a * b * c) := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - a * c), sq_nonneg (a * c - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    linarith
    positivity
  linarith