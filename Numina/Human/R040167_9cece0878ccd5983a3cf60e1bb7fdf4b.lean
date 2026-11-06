import Mathlib
/- Soit $x, y$ des réels. Montrer que:

$$
|x|+|y| \leqslant|x-y|+|x+y| .
$$ -/
theorem algebra_607258 (x y : ℝ) : |x| + |y| ≤ |x - y| + |x + y|:= by
  -- By triangle inequality, |a + b| ≤ |a| + |b|
  -- Here we use its reverse form: |a| + |b| ≥ |a + b|
  have h1 : |x - y| + |x + y| ≥ |(x - y) + (x + y)|:= by exact abs_add_le (x - y) (x + y)
  -- Similarly apply the triangle inequality for subtraction
  have h2 : |x - y| + |x + y| ≥ |(x - y) - (x + y)|:= by exact abs_sub (x - y) (x + y)
  -- Simplify the algebraic expressions
  ring_nf at h1 h2
  -- Simplify numerical expressions
  norm_num at h1 h2
  -- Use the property |a * b| = |a| * |b| for the first equation
  rw [show |x * 2| = |x| * |2| by exact abs_mul x 2] at h1
  -- Use the same property for the second equation
  rw [show |y * 2| = |y| * |2| by exact abs_mul y 2] at h2
  -- Simplify numerical expressions again
  norm_num at h1 h2
  -- Complete the proof using linear arithmetic
  linarith
