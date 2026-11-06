import Mathlib

open Real
set_option maxHeartbeats 800000
theorem inequalities_35861     (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    3 / 2 ≤ (b ^ 2 + c ^ 2 - a ^ 2) / (a * (b + c)) +
    (c ^ 2 + a ^ 2 - b ^ 2) / (b * (c + a)) +
    (a ^ 2 + b ^ 2 - c ^ 2) / (c * (a + b)) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : 0 < a * (b + c) := by
    apply mul_pos
    exact ha
    linarith
  have h3 : 0 < b * (c + a) := by
    apply mul_pos
    exact hb
    linarith
  have h4 : 0 < c * (a + b) := by
    apply mul_pos
    exact hc
    linarith
  have h5 : (b ^ 2 + c ^ 2 - a ^ 2) / (a * (b + c)) + (c ^ 2 + a ^ 2 - b ^ 2) / (b * (c + a)) + (a ^ 2 + b ^ 2 - c ^ 2) / (c * (a + b)) - 3 / 2 ≥ 0 := by
    have h6 : 0 < a * b * c * (b + c) * (c + a) * (a + b) := by
      positivity
    have h7 : (b ^ 2 + c ^ 2 - a ^ 2) / (a * (b + c)) + (c ^ 2 + a ^ 2 - b ^ 2) / (b * (c + a)) + (a ^ 2 + b ^ 2 - c ^ 2) / (c * (a + b)) - 3 / 2 =
        ( (b ^ 2 + c ^ 2 - a ^ 2) * b * c * (c + a) * (a + b) +
          (c ^ 2 + a ^ 2 - b ^ 2) * a * c * (b + c) * (a + b) +
          (a ^ 2 + b ^ 2 - c ^ 2) * a * b * (b + c) * (c + a) - (3 / 2) * (a * b * c * (b + c) * (c + a) * (a + b)) ) / (a * b * c * (b + c) * (c + a) * (a + b)) := by 
      field_simp 
      ring
    rw [h7] at *
    apply div_nonneg
    nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
              sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
              sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
              mul_pos ha (show 0 < a * b by nlinarith),
              mul_pos ha (show 0 < a * c by nlinarith),
              mul_pos hb (show 0 < b * c by nlinarith)
            ]
    all_goals positivity
  linarith