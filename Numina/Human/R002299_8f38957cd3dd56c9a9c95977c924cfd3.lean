import Mathlib

/- The population of the United States in 1980 was $226,504,825$.  The area of the country is $3,615,122$ square miles.  The are $(5280)^{2}$ square feet in one square mile.  Which number below best approximates the average number of square feet per person?

$ \textbf{(A)}\ 5,000\qquad\textbf{(B)}\ 10,000\qquad\textbf{(C)}\ 50,000\qquad\textbf{(D)}\ 100,000\qquad\textbf{(E)}\ 500,000 $-/
theorem algebra_82405 (population : ℕ) (area1 area2: ℕ) {aver : ℝ} (h0 : pop = 226504825) (h1 : area1 = 3615122)
  (h2 : area2 = (5280) ^ 2 * area1) (h : aver = area2 / pop)
     : |aver- 500000| < |aver - 100000| ∧ |aver- 500000| < |aver - 50000| ∧ |aver- 500000| < |aver - 10000| ∧ 
    |aver - 500000| < |aver - 5000| 
    := by
  constructor
  rw [h, h0, h2, h1]
  norm_num
  unfold abs
  simp
  left
  constructor
  linarith
  linarith
  constructor
  rw [h, h0, h2, h1]
  norm_num
  unfold abs
  simp
  left
  constructor
  linarith
  linarith
  constructor
  rw [h, h0, h2, h1]
  norm_num
  unfold abs
  simp
  left
  constructor
  linarith
  linarith
  rw [h, h0, h2, h1]
  norm_num
  unfold abs
  simp
  left
  constructor
  linarith
  linarith
