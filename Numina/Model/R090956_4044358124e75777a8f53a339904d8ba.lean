import Mathlib

open Real

theorem inequalities_1362 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a ^ 3 / ((1 + b) * (1 + c)) + b ^ 3 / ((1 + c) * (1 + a)) +
    c ^ 3 / ((1 + a) * (1 + b)) ≥ 3 / 4 := by
    have h1 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
    have h2 : a ^ 3 * (1 + a) + b ^ 3 * (1 + b) + c ^ 3 * (1 + c) ≥ 3 / 4 * ((1 + a) * (1 + b) * (1 + c)) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    have h3 : a ^ 3 / ((1 + b) * (1 + c)) + b ^ 3 / ((1 + c) * (1 + a)) +
        c ^ 3 / ((1 + a) * (1 + b)) =
        (a ^ 3 * (1 + a) + b ^ 3 * (1 + b) + c ^ 3 * (1 + c)) / ((1 + a) * (1 + b) * (1 + c)) := by
      field_simp
      ring
    rw [h3]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith [h2]