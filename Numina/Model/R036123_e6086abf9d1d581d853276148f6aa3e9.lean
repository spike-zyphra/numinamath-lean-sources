import Mathlib

theorem inequalities_146852 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 5 ≤ (b + c - a)^2 / ((b + c)^2 + a^2) +
        (c + a - b)^2 / ((c + a)^2 + b^2) +
        (a + b - c)^2 / ((a + b)^2 + c^2) := by 
  have h1 : 0 < (b + c) ^ 2 + a ^ 2 := by
    positivity
  have h2 : 0 < (c + a) ^ 2 + b ^ 2 := by
    positivity
  have h3 : 0 < (a + b) ^ 2 + c ^ 2 := by
    positivity
  have h4 : (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) - 3 / 5 ≥ 0 := by
    have h5 : (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) - 3 / 5 =
        ( (b + c - a) ^ 2 * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) +
          (c + a - b) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((a + b) ^ 2 + c ^ 2) + 
          (a + b - c) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) - (3 / 5) * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) ) / ( ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) ) := by
      field_simp
      ring 
    rw [h5]
    have h6 : ( (b + c - a) ^ 2 * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) +
        (c + a - b) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((a + b) ^ 2 + c ^ 2) + 
        (a + b - c) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) - (3 / 5) * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) ) ≥ 0 := by
      nlinarith [ 
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    have h9 : ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) > 0 := by
      positivity
    apply div_nonneg
    · linarith
    · positivity
  linarith