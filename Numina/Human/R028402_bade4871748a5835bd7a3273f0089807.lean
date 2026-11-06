import Mathlib

/- Show that, for all real $x, y, z$ :


$$

|x|+|y|+|z| \leqslant|x+y-z|+|y+z-x|+|z+x-y| \text {. }

$$
 -/
theorem inequalities_154508 (x y z : ℝ) : |x| + |y| + |z| ≤ |x + y - z| + |y + z - x| + |z + x - y| := by
  -- prove a lemma that 2|a| ≤ |a+b-c| + |a+c-b|
  have aux (a b c : ℝ) : 2 * |a| ≤ |a + b - c| + |a + c - b| := by calc
    2 * |a| = |2| * |a| := by congr; norm_num
    _ = |2 * a| := by exact Eq.symm (abs_mul 2 a)
    _ = |(a + b - c) + (a + c - b)| := by ring_nf
    _ ≤ |a + b - c| + |a + c - b| := by exact abs_add_le (a + b - c) (a + c - b)
  -- apply lemma on x, y, z 3 times and linear maniuplation with those 3 inequailtiy proves target
  have h₁ := aux x y z
  have h₂ := aux y z x
  have h₃ := aux z x y
  ring_nf at *
  linarith