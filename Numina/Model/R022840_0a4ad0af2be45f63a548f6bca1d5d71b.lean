import Mathlib.Tactic

theorem inequalities_124744 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    2/3 ≤ a/(b + 2*c + 3*d) + b/(c + 2*d + 3*a) + c/(d + 2*a + 3*b) +
    d/(a + 2*b + 3*c) := by
  have h1 : 0 < b + 2 * c + 3 * d := by linarith
  have h2 : 0 < c + 2 * d + 3 * a := by linarith
  have h3 : 0 < d + 2 * a + 3 * b := by linarith
  have h4 : 0 < a + 2 * b + 3 * c := by linarith
  have h37 : a/(b + 2*c + 3*d) + b/(c + 2*d + 3*a) + c/(d + 2*a + 3*b) +
      d/(a + 2*b + 3*c) - 2/3 ≥ 0 := by
    have h1' : 0 < (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c) := by
      positivity
    have h6 : a/(b + 2*c + 3*d) + b/(c + 2*d + 3*a) + c/(d + 2*a + 3*b) +
        d/(a + 2*b + 3*c) - 2/3 =
        (a * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c) +
         b * (b + 2 * c + 3 * d) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c) +
         c * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (a + 2 * b + 3 * c) +
         d * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) -
         2/3 * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c)) / 
        ((b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c)) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * (c + 2 * d + 3 * a) - b * (b + 2 * c + 3 * d)), sq_nonneg (b * (d + 2 * a + 3 * b) - c * (c + 2 * d + 3 * a)), sq_nonneg (c * (a + 2 * b + 3 * c) - d * (d + 2 * a + 3 * b)), sq_nonneg (d * (b + 2 * c + 3 * d) - a * (a + 2 * b + 3 * c)), mul_pos ha hb, mul_pos hb hc, mul_pos hc hd, mul_pos ha hc, mul_pos ha hd, mul_pos hb hd, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a), sq_nonneg (a - c), sq_nonneg (b - d),
      mul_pos (show (0 : ℝ) < a from ha) (show (0 : ℝ) < b from hb), 
      mul_pos (show (0 : ℝ) < b from hb) (show (0 : ℝ) < c from hc), 
      mul_pos (show (0 : ℝ) < c from hc) (show (0 : ℝ) < d from hd), 
      mul_pos (show (0 : ℝ) < a from ha) (show (0 : ℝ) < d from hd), 
      mul_pos (show (0 : ℝ) < a from ha) (show (0 : ℝ) < c from hc), 
      mul_pos (show (0 : ℝ) < b from hb) (show (0 : ℝ) < d from hd)
      ]
    positivity
  linarith