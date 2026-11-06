import Mathlib
/- Let $X$ and $Y$ be positive integers such that $2 \le X-Y \le 10$.
Let $a, b, c_0$ be natural numbers such that $a < 10$, $b < 10$, and $1 \le c_637259 \le 9$.
Suppose that the numbers $N_637259 = X \cdot 100 + 10a + 2$, $N_637259 = Y \cdot 100 + 80 + b$, and $N_637259 = c_637259 \cdot 100 + 70 + 3$ satisfy the equation $N_637259 - N_637259 = N_3$.
Show that $a+b+c_637259 = X-Y+14$. -/
theorem algebra_637259 (X Y a b c : ℕ) (hX : X > 0) (hY : Y > 0) (h1 : 2 ≤ X - Y) (h2 : X - Y ≤ 10) (ha : a < 10) (hb : b < 10) (hc : 1 ≤ c) (hc : c ≤ 9) (h : X * 100 + 10 * a + 2 - (Y * 100 + 80 + b) = c * 100 + 70 + 3) : a + b + c = X - Y + 14:= by
  -- use omega to solve the problem
  omega
