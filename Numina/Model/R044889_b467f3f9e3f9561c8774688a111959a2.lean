import Mathlib

theorem inequalities_123152 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : y^3 + y ≤ x - x^3) :
    y < x ∧ x < 1 ∧ x^2 + y^2 < 1 := by 
  constructor
  · -- Prove y < x
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, 
      sq_nonneg (x - y), sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), 
      sq_nonneg (x - 1), sq_nonneg (y - 1),
      sq_pos_of_pos (show (0 : ℝ) < x by linarith), sq_pos_of_pos (show (0 : ℝ) < y by linarith),
      mul_pos hx hy
    ]
  constructor
  · -- Prove x < 1
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, 
      sq_nonneg (x - 1), sq_nonneg (y - 1), 
      sq_pos_of_pos (show (0 : ℝ) < x by linarith), sq_pos_of_pos (show (0 : ℝ) < y by linarith), 
      mul_pos hx hy, sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1)
    ]
  · -- Prove x^2 + y^2 < 1
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, 
      sq_nonneg (x - 1), sq_nonneg (y - 1), 
      sq_pos_of_pos (show (0 : ℝ) < x by linarith), sq_pos_of_pos (show (0 : ℝ) < y by linarith), 
      mul_pos hx hy, sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1)
    ]