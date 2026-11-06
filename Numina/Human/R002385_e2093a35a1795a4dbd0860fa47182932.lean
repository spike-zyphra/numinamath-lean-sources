import Mathlib

/- Let $a$ and $b$ be two positive integers satifying $gcd(a, b) = 1$. Consider a pawn standing on the grid point $(x, y)$. 
A step of type A consists of moving the pawn to one of the following grid points: $(x+a, y+a),(x+a,y-a), (x-a, y + a)$ or $(x - a, y - a)$. 
A step of type B consists of moving the pawn to $(x + b,y + b),(x + b,y - b), (x - b,y + b)$ or $(x - b,y - b)$.
Now put a pawn on $(0, 0)$. You can make a (nite) number of steps, alternatingly of type A and type B, starting with a step of type A. You can make an even or odd number of steps, i.e., the last step could be of either type A or type B. 
Determine the set of all grid points $(x,y)$ that you can reach with such a series of steps. -/
theorem number_theory_90500 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.gcd a b = 1) :
    {(x, y) : ℤ × ℤ | ∃ n m, x = a * n - b * m ∧ y = a * n + b * m} =
    {(x, y) : ℤ × ℤ | ∃ m n, x = a * m - b * n ∧ y = a * m + b * n} := by 
  ext ⟨x, y⟩
  constructor <;> simp_all <;> aesop