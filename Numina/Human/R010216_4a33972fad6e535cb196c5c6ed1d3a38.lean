import Mathlib

/-If $x$ and $y$ are positive integers less than $20$ for which $x + y + xy = 76$, what is the value of $x + y$?

The final answer is $ \boxed{16} $-/
theorem algebra_10922 {x y : ℕ} (xpos : 0 < x) (ypos : 0 < y) (hx : x < 20) (hy : y < 20)
 (h : x + y + x * y = 76) : x + y = 16 := by
  -- If we add $1$ to both sides of the equation, the left hand side may be factored using Simon's Favorite Factoring Trick.
  -- Thus, $$xy + x + y + 1 = (x+1)(y+1) = 77.$$
  have h1 : (x + 1) * (y + 1) = 77 := by linarith
  -- Since $x,y$ are positive integers, then $x+1, y+1$ must be a pair of factors of $77$, which are given by $\{x+1,y+1\} = \{1,77\},\{7,11\}$.
  -- Thus, $\{x,y\} = \{0,76\},\{6,10\}$, though only the latter satisfies the given conditions.
  have h2 : x = 6 ∧ y = 10 ∨ x = 10 ∧ y = 6 := by
    have : x + 1 ∣ 77 := Dvd.intro (y + 1) h1
    interval_cases x <;> omega
  -- Hence, $x+y = 6 + 10 = \boxed{16}$.
  rcases h2 with h2 | h2 <;> linarith
