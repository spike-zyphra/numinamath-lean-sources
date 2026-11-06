import Mathlib

theorem inequalities_25273 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 2*a*b*c + a*b + b*c + c*a = 1) :
    (a + 1) / ((a + 1)^2 + (b + 1)^2) +
    (b + 1) / ((b + 1)^2 + (c + 1)^2) +
    (c + 1) / ((c + 1)^2 + (a + 1)^2) ≤ 1 := by
  have h1 : 0 < (a + 1) := by linarith
  have h2 : 0 < (b + 1) := by linarith
  have h3 : 0 < (c + 1) := by linarith
  have h11 : 0 < (a + 1)^2 + (b + 1)^2 := by positivity
  have h12 : 0 < (b + 1)^2 + (c + 1)^2 := by positivity
  have h13 : 0 < (c + 1)^2 + (a + 1)^2 := by positivity
  have h14 : (a + 1) / ((a + 1)^2 + (b + 1)^2) ≤ 1 / (2 * (b + 1)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - b)]
  have h15 : (b + 1) / ((b + 1)^2 + (c + 1)^2) ≤ 1 / (2 * (c + 1)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b - c)]
  have h16 : (c + 1) / ((c + 1)^2 + (a + 1)^2) ≤ 1 / (2 * (a + 1)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c - a)]
  have h20 : (a + 1) / ((a + 1)^2 + (b + 1)^2) + (b + 1) / ((b + 1)^2 + (c + 1)^2) + (c + 1) / ((c + 1)^2 + (a + 1)^2) ≤ 1 / (2 * (b + 1)) + 1 / (2 * (c + 1)) + 1 / (2 * (a + 1)) := by 
    linarith [h14, h15, h16]
  have h21 : 1 / (2 * (b + 1)) + 1 / (2 * (c + 1)) + 1 / (2 * (a + 1)) ≤ 1 := by
    have h4 : 0 < (a + 1) * (b + 1) * (c + 1) := by positivity
    have h22 : 1 / (2 * (b + 1)) + 1 / (2 * (c + 1)) + 1 / (2 * (a + 1)) - 1 ≤ 0 := by
      have h23 : (1 / (2 * (b + 1)) + 1 / (2 * (c + 1)) + 1 / (2 * (a + 1)) - 1) = 
        ( (c + 1) * (a + 1) + (b + 1) * (a + 1) + (b + 1) * (c + 1) - 2 * (a + 1) * (b + 1) * (c + 1) ) / ( 2 * (a + 1) * (b + 1) * (c + 1) ) := by
        field_simp
        ring
      rw [h23]
      have h24 : (c + 1) * (a + 1) + (b + 1) * (a + 1) + (b + 1) * (c + 1) - 2 * (a + 1) * (b + 1) * (c + 1) ≤ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
        ]
      apply div_nonpos_of_nonpos_of_nonneg h24 (by positivity)
    linarith 
  linarith [h20, h21]