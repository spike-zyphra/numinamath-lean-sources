import Mathlib

theorem inequalities_598750 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) ≥ 3 / 2 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h21 : 1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) - 3 / 2 ≥ 0 := by
    have pos1 : 0 < a ^ 2 * (b + c) := by positivity
    have pos2 : 0 < b ^ 2 * (c + a) := by positivity
    have pos3 : 0 < c ^ 2 * (a + b) := by positivity
    have pos4 : 0 < a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b) := by positivity
    have h24 : (1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) - 3 / 2) =
        ( b ^ 2 * c ^ 2 * (c + a) * (a + b) + a ^ 2 * c ^ 2 * (b + c) * (a + b) + a ^ 2 * b ^ 2 * (b + c) * (c + a) - 3 / 2 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b)) ) / (a^2 * (b + c) * b^2 * (c + a) * c^2 * (a + b)) := by
      field_simp
      ring
    rw [h24] at *
    apply div_nonneg
    · -- To prove numerator is positive
      have h25 : a * b * c = 1 := habc
      have h26 : b ^ 2 * c ^ 2 * (c + a) * (a + b) + a ^ 2 * c ^ 2 * (b + c) * (a + b) + a ^ 2 * b ^ 2 * (b + c) * (c + a) - 3 / 2 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b)) ≥ 0 := by
        rw [show a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b) = (a * b * c)^2 * ((b + c) * (c + a) * (a + b)) by 
          ring_nf
        ]
        rw [show a * b * c = 1 by linarith [h25]]
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
                sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
                sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
                sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
                sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
                mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity), 
                mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity), 
                sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)
              ]
      linarith
    all_goals
      positivity
  linarith