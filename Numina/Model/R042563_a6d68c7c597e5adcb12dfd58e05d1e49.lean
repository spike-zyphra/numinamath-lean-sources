import Mathlib

theorem inequalities_602754 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b + c + d = 4) :
    a * b * (a + b + 2 * c) + b * c * (b + c + 2 * d) + c * d * (c + d + 2 * a) +
    d * a * (d + a + 2 * b) ≤ 16 := by

  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have h2 : 0 ≤ (a - c) ^ 2 := sq_nonneg (a - c)
  have h3 : 0 ≤ (a - d) ^ 2 := sq_nonneg (a - d)
  have h4 : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
  have h5 : 0 ≤ (b - d) ^ 2 := sq_nonneg (b - d)
  have h6 : 0 ≤ (c - d) ^ 2 := sq_nonneg (c - d)
  have h7 : 0 ≤ (a + b - c - d) ^ 2 := sq_nonneg (a + b - c - d)
  have h8 : 0 ≤ (a + c - b - d) ^ 2 := sq_nonneg (a + c - b - d)
  have h9 : 0 ≤ (a + d - b - c) ^ 2 := sq_nonneg (a + d - b - c)
  have h10 : 0 ≤ a * b := mul_nonneg ha hb
  have h11 : 0 ≤ a * c := mul_nonneg ha hc
  have h12 : 0 ≤ a * d := mul_nonneg ha hd
  have h13 : 0 ≤ b * c := mul_nonneg hb hc
  have h14 : 0 ≤ b * d := mul_nonneg hb hd
  have h15 : 0 ≤ c * d := mul_nonneg hc hd
  
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c), 
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha hd, 
          mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg hc hd, 
          mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ c * d by nlinarith), 
          mul_nonneg (show 0 ≤ a * c by nlinarith) (show 0 ≤ b * d by nlinarith)
        ]