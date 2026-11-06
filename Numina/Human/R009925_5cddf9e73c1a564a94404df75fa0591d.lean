import Mathlib
open Mathlib
/--
Oscar buys $13$ pencils and $3$ erasers for $1.00$. A pencil costs more than an eraser, and both items cost a [whole number](https://artofproblemsolving.com/wiki/index.php/Whole_number) of cents. What is the total cost, in cents, of one pencil and one eraser?
$\mathrm{(A)}\ 10\qquad\mathrm{(B)}\ 12\qquad\mathrm{(C)}\ 15\qquad\mathrm{(D)}\ 18\qquad\mathrm{(E)}\ 20$
-/
lemma algebra_1169 (p e : ℕ) (h : 13 * p + 3 * e = 100) (h1 : p > e) : p + e = 10 := by
  -- Let the price of a pencil be $p$ and an eraser $e$.  Then $13p + 3e = 100$ with $p > e > 0$.  Since $p$ and $e$ are [positive integers](https://artofproblemsolving.com/wiki/index.php/Positive_integer), we must have $e \geq 1$ and $p \geq 2$.
  have s1 : e ≥ 1 := by omega
  have s2 : p ≥ 2 := by omega
  -- Considering the [equation](https://artofproblemsolving.com/wiki/index.php/Equation) $13p + 3e = 100$ [modulo](https://artofproblemsolving.com/wiki/index.php/Modulo) 3 (that is, comparing the [remainders](https://artofproblemsolving.com/wiki/index.php/Remainder) when both sides are divided by 3) we have $p + 0e \equiv 1 \pmod 3$ so $p$ leaves a remainder of 1 on division by 3.
  have s3 : p = 3 * (p / 3) + 1 := by omega
  -- Since $p ≥ 2$, possible values for $p$ are 4, 7, 10 ....
  -- Since 13 pencils cost less than 100 cents, $13p < 100$. 
  have s4 : 13 * p < 100 := by omega
  -- $13 × 10 = 130$ is too high, so $p$ must be 4 or 7.
  have s5 : p = 4 ∨ p = 7 := by omega
  -- If $p = 4$ then $13p = 52$ and so $3e = 48$ giving $e = 16$.
  have s6 : p = 4 → e = 16 := by omega
  -- This contradicts the pencil being more expensive.
  have s7 : p ≠ 4 := by omega
  -- The only remaining value for $p$ is 7
  have s8 : p = 7 := by omega
  -- e = (100 - 13 * 7)/3
  have s9 : e = (100 - 13 * 7) / 3 := by omega
  -- e = 3
  norm_num at s9
  -- p + e = 10
  rw [s8, s9]