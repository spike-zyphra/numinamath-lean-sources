import Mathlib

theorem algebra_304 (a b c d : ℝ) (a' : a ≤ b ∧ b ≤ c ∧ c ≤ d)
    (hmedian : (b + c) / 2 = 80) (hdiff : d - a = 12) : (a + b + c + d) / 4 ≤ 83 := by
  rcases a' with ⟨ha1, ha2, ha3⟩
  have h1 : b + c = 160 := by
    linarith
  have h2 : d = a + 12 := by 
    linarith
  nlinarith [sq_nonneg (a - 80), sq_nonneg (b - 80), sq_nonneg (c - 80), sq_nonneg (d - 92), 
    hmedian, hdiff, ha1, ha2, ha3, 
    show b ≤ 80 by nlinarith [ha2, h1], 
    show c ≥ 80 by nlinarith [ha2, h1], 
    show d ≥ c by linarith [ha3]
  ]
  all_goals linarith