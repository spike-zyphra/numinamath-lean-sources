import Mathlib

theorem algebra_116694 (a b c : ℝ) (ha : 0 < c) (h : a + b > c) (h' : |a - b| < c)
    (x : ℝ) (hx : a^2 * x^2 + (b^2 + a^2 - c^2) * x + b^2 = 0) :
    False := by
  have h1 : a - b > -c := by 
    cases' abs_lt.mp h' with h2 h3
    linarith
  have h2 : a - b < c := by
    cases' abs_lt.mp h' with h2 h3
    linarith
  have h3 : (a - b) ^ 2 < c ^ 2 := by nlinarith [abs_lt.mp h']
  have h4 : (a + b) ^ 2 > c ^ 2 := by nlinarith [abs_lt.mp h']
  have h5 : (b ^ 2 + a ^ 2 - c ^ 2) ^ 2 - 4 * (a ^ 2) * (b ^ 2) < 0 := by
    have h6 : (a - b) ^ 2 - c ^ 2 < 0 := by
      nlinarith [abs_lt.mp h']
    have h7 : (a + b) ^ 2 - c ^ 2 > 0 := by
      nlinarith [abs_lt.mp h']
    have h8 : ((a - b) ^ 2 - c ^ 2) * ((a + b) ^ 2 - c ^ 2) < 0 := by
      apply mul_neg_of_neg_of_pos
      · linarith
      · linarith
    nlinarith [show (b ^ 2 + a ^ 2 - c ^ 2) ^ 2 - 4 * (a ^ 2) * (b ^ 2) = ((a - b) ^ 2 - c ^ 2) * ((a + b) ^ 2 - c ^ 2) by 
      nlinarith [sq_nonneg (a * b), sq_nonneg (a^2 - b^2)]
    ]
  nlinarith [sq_nonneg (a^2 * x + (b^2 + a^2 - c^2) / 2), sq_nonneg (a * x * c + b * c), sq_nonneg ((a + b) * x), sq_nonneg ((a - b) * x), sq_nonneg (a * x), sq_nonneg (b * x), mul_pos (show 0 < c by linarith) (show 0 < c by linarith), sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos (show 0 < a + b - c by nlinarith) (show 0 < c by nlinarith), mul_pos (show 0 < c by nlinarith) (show 0 < a + b - c by nlinarith), h5]