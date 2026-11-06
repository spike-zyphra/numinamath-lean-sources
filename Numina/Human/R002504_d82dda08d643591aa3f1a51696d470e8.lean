import Mathlib

/- Real numbers x and y satisfy the equation x^2+y^2=10x−6y−34 . What is x+y?
(A) 1
(B) 2
(C) 3
(D) 6
(E) 8 -/

theorem algebra_94324 {x y : ℝ} (h : x^2 + y^2 = 10 * x - 6 * y - 34) : x + y = 2 := by
  -- manipulate equation to x^2 - 10x + 25 + y^2 + 6y + 9 = 0 as this'll allow to use square formula and get (x-5)^2 + (y+3)^2 = 0
  have h' : (x^2 - 10 * x + 25) + (y^2 + 6*y + 9) = 0 := by linarith
  have h' : (x - 5)^2 + (y + 3)^2 = 0 := by linarith
  -- sum of two square imply both squares are 0
  have hx: 0 ≤ (x-5)^2 := by exact sq_nonneg (x-5)
  have hy: 0 ≤ (y+3)^2 := by exact sq_nonneg (y+3)
  have hz : (x - 5) ^ 2 = 0 ∧ (y + 3) ^ 2 = 0 := (add_eq_zero_iff_of_nonneg hx hy).1 h'
  -- squares being zero means the values themselves are zero, this provides x = 5, y = -3, plug in to get value
  have hzx : x - 5 = 0 := by exact sq_eq_zero_iff.1 hz.1
  have hzy : y + 3 = 0 := by exact sq_eq_zero_iff.1 hz.2
  linarith