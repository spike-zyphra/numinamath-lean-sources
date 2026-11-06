import Mathlib

/-Let $b$ be an integer base, $b \ge 2$. Let $x$ be an integer such that $0 \le x < b$.
Suppose that $x$ satisfies the equation
$$(-(8053873881207597 \cdot b + x))^3 + (80435758145817515)^3 + (12602123297335631)^3 = 42.$$
It is given that for $b=10$, the solution is $x=4$.
Determine the value of $x$ if $b=11$. You should assume that a unique such integer $x$ exists in the specified range for $b=11$. Show the answer is $x=9$.-/

theorem number_theory_636731 (b x: ℤ) (hb: b = 10)
  (h: ∀ y, 0 ≤ y → y < b → (-(8053873881207597 * b + y))^3 + (80435758145817515)^3 + (12602123297335631)^3 = 42 → y = x):
  x = 4 := by

  set y:= (4: ℤ)
  specialize h y
  symm
  apply h (by simp [y]) (by simp [y, hb])
  simp [y, hb]