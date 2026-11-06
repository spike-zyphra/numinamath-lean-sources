import Mathlib

theorem number_theory_303131 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : 2 * x^2 + 3 * y^2 = 4 * x^2 * y^2 + 1) :
    x^2 + y^2 = 2 := by
  have h1 : x ≤ 2 := by 
    by_contra h1
    push_neg at h1
    have h2 : y ≤ 2 := by
      nlinarith [sq_nonneg (x * y), sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ),
        h, h1, mul_pos (show 0 < (x : ℕ) by linarith) (show 0 < (y : ℕ) by linarith)]
    interval_cases y <;> try { 
      all_goals nlinarith 
    }
  have h2 : y ≤ 2 := by 
    by_contra h2
    push_neg at h2 
    have h3 : x ≤ 2 := by
      nlinarith [sq_nonneg (x * y), sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ),
        h, h2, mul_pos (show 0 < (x : ℕ) by linarith) (show 0 < (y : ℕ) by linarith)]
    interval_cases x <;> try { 
      all_goals nlinarith 
    }
  interval_cases x <;> interval_cases y 
    <;> omega