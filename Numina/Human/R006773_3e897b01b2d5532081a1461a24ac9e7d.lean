import Mathlib
/- Let a four-digit natural number be denoted by $\overline{abcd}$, where $a, b, c, d$ are its digits, $a \neq 0$. Let $\overline{abc}$ denote the number $100a+10b+c$, $\overline{ab}$ denote $10a+b$. It is known that the relation $\overline{abcd} - \overline{abc} - \overline{ab} - a = K$ holds for some integer $K$.
If $K=2779$, determine the four-digit number $\overline{abcd}$. Show that the answer is $3125$. -/
theorem algebra_641054 (a b c : ℕ) (ha : a ≤ 9) (hb : b ≤ 9) (hc : c ≤ 9) (hd : d ≤ 9) (h : a ≠ 0) : 1000 * a + 100 * b + 10 * c + d - (100 * a + 10 * b + c) - (10 * a + b) - a = 2779 → 1000 * a + 100 * b + 10 * c + d = 3125:= by
  -- Introduce the hypothesis that the equation equals 2779
  intro h1
  -- Simplify the left side of the equation to 889*a + 89*b + 9*c + d = 2779
  rw [show 1000 * a + 100 * b + 10 * c + d - (100 * a + 10 * b + c) - (10 * a + b) - a = 889 * a + 89 * b + 9 * c + d by omega] at h1
  -- Determine that a = 3 using omega (arithmetic solver)
  have h2 : a = 3:= by omega
  -- Substitute a = 3 into the goal
  subst a
  -- Determine that b = 1 using omega
  have h2 : b = 1:= by omega
  -- Substitute b = 1 into the goal
  subst b
  -- Determine that c = 2 using omega
  have h2 : c = 2:= by omega
  -- Substitute c = 2 into the goal
  subst c
  -- Determine that d = 5 using omega
  have h2 : d = 5:= by omega
  -- Substitute d = 5 into the goal
  subst d
  -- Simplify to show 3125 = 3125
  simp
