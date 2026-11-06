import Mathlib

theorem inequalities_597262 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a ^ 2 + b ^ 2 + c ^ 2 + 2 * Real.sqrt (3 * a * b * c) ≤ 1 := by

  have h4 : a ^ 2 + b ^ 2 + c ^ 2 = 1 - 2 * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (a + b + c - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

  rw [h4]

  have h5 : Real.sqrt (3 * a * b * c) ≤ a * b + b * c + c * a := by
    have h6 : Real.sqrt (3 * a * b * c) ≥ 0 := Real.sqrt_nonneg (3 * a * b * c)
    have h7 : (a * b + b * c + c * a) ≥ 0 := by nlinarith

    have h5' : (Real.sqrt (3 * a * b * c)) ^ 2 ≤ (a * b + b * c + c * a) ^ 2 := by
      have h8 : (Real.sqrt (3 * a * b * c)) ^ 2 = 3 * a * b * c := Real.sq_sqrt (by positivity)
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        mul_nonneg (show 0 ≤ a * b by positivity) (show 0 ≤ b * c by positivity),
        mul_nonneg (show 0 ≤ b * c by positivity) (show 0 ≤ c * a by positivity),
        mul_nonneg (show 0 ≤ c * a by positivity) (show 0 ≤ a * b by positivity) ]

    have h9 : Real.sqrt (3 * a * b * c) ≤ a * b + b * c + c * a := by
      nlinarith [Real.sqrt_nonneg (3 * a * b * c), h6, h5', h7, mul_nonneg (show 0 ≤ a * b by positivity) (show 0 ≤ b * c by positivity), mul_nonneg (show 0 ≤ b * c by positivity) (show 0 ≤ c * a by positivity), mul_nonneg (show 0 ≤ c * a by positivity) (show 0 ≤ a * b by positivity) ]
    linarith

  linarith [h5]