import Mathlib

/-Let $b$ be an integer greater than 1, and let $d$ be a non-negative integer such that
$0 \leq d < b$. Two positive integers $x$ and $y$ each have a units digit of $d$ when expressed in base $b$.
Find the units digit of their product $x \cdot y$ when expressed in base $b$. Show the answer is $d^2 \pmod b$.-/

theorem number_theory_635579 (b d x y: ℕ) (h3: x % b = d) (h4: y % b = d):
  (x * y) % b = d ^ 2 % b := by

  rw [Nat.mul_mod, h3, h4]
  rw [show d ^ 2 = d * d by ring]
