import Mathlib

-- Let $f(n)$ denote the number of ways to fill a $2 \times n$ board. One can fill the leftmost column with two $1 \times 1$ tiles, leaving $f(n-1)$ ways, or one can fill the leftmost two columns with one $2 \times 2$ tile, leaving $f(n-2)$ ways. Therefore, $f(n)=f(n-1)+f(n-2)$
def f (n : ℕ) : ℕ := match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => f n + f (n + 1)

/-How many ways can one tile a 2×8 board with 
1×1 and 2×2 tiles? 
Rotations and reflections of the same configuration are considered distinct.-/

theorem Combinatorics_610027: f 8 = 34 := by
  simp [f]