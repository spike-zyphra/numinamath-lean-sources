import Mathlib

theorem algebra_326959 (a b c : ℤ) (ha : a + b = 2006) (hc : c - a = 2005) (h : a < b) :
    a + b + c ≤ 5013 := by
  have ha1 : b = 2006 - a := by linarith
  have hc1 : c = a + 2005 := by linarith
  rw [hc1, ha1]
  -- Now $a + b + c = a + (2006 - a) + (a + 2005) = a + 4011$
  -- We need to show $a + 4011 \leq 5013$, i.e., $a \leq 1002$.
  have h1 : a < 2006 - a := by
    linarith
  -- Solving $a < 2006 - a$ gives $2a < 2006$ so $a < 1003$.
  have h2 : a < 1003 := by
    omega
  -- Since $a < 1003$, the maximum integer value of $a$ is 1002.
  -- Therefore, $a + 4011 \leq 1002 + 4011 = 5013$.
  omega